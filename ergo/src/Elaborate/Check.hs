{-# Language ImportQualifiedPost #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Check where

import Control.Monad (unless)
import Control.Lens hiding (Context)
import Elaborate.Error
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value
import Elaborate.Unification
import Icit
import Names
import Source.Term qualified as Raw
import System.IO.Unsafe (unsafeInterleaveIO)

-- | Define a new variable.
define :: Name -> VTy -> Val -> Context -> Context
define x a t (Context vs tys ns no d) =
  Context (VDef vs t) (TySnoc tys Def a) (x:ns) (NOSource:no) (d + 1)

-- | Insert fresh implicit applications.
insert' :: Context -> IO (TM, VTy) -> IO (TM, VTy)
insert' cxt act = do
  (t0, va0) <- act
  let go t va = force va >>= \case
        VPi _ Implicit a b -> do
          m <- freshMeta cxt a
          mv <- eval (cxt^.vals) m
          mv' <- b mv
          go (App Implicit t m) mv'
        va' -> pure (t, va')
  go t0 va0

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Context -> IO (TM, VTy) -> IO (TM, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Implicit _ _), va) -> pure (t, va)
  (t                     , va) -> insert' cxt (pure (t, va))

infer :: Context -> Raw.Term -> IO (TM, VTy)
infer cxt = \case
  Raw.Loc p t -> addSourcePos p (infer cxt t)

  Raw.U -> pure (U, VU)

  Raw.Var x -> do
    let go :: [Name] -> [NameOrigin] -> Types -> Int -> IO (TM, VTy)
        go (y:_) (NOSource:_) (TySnoc _ _ a) i | SourceName x 0 == y = pure (Var i,a)
        go (_:xs) (_:os) (TySnoc as _ _) i = go xs os as (i + 1)
        go [] [] TyNil _ = report (cxt^.names) $ NameNotInScope (SourceName x 0)
        go _ _ _ _ = panic
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  Raw.Pi x i a b -> do
    a' <- check cxt a VU
    va <- eval (cxt^.vals) a'
    b' <- check (bind (sourceName x) NOSource va cxt) b VU
    pure (Pi (sourceName x) i a' b', VU)

  Raw.App i t0 u -> do
    (t, va) <- case i of 
      Explicit -> insert' cxt $ infer cxt t0
      _        -> infer cxt t0
    force va >>= \case
      VPi _ i' a b -> do
        unless (i == i') $
          report (cxt^.names) $ IcitMismatch i i'
        u' <- check cxt u a
        o <- eval (cxt^.vals) u' >>= b
        pure (App i t u', o)
      VNe (HMeta m) sp -> do
        (m',a0) <- freshMeta' cxt VU 
        a <- eval (cxt^.vals) a0
        let x = metaName m'
        c <- freshMeta (bind x NOInserted a cxt) VU
        let b x' = eval (VDef (cxt^.vals) x') c
        unifyWhile cxt (VNe (HMeta m) sp) (VPi x i a b)
        u' <- check cxt u a
        ty <- eval (cxt^.vals) u' >>= b
        pure (App i t u', ty)
      _ -> do
        r <- unsafeInterleaveIO (uneval (cxt^.len) va)
        report (cxt^.names) $ ExpectedFunction r

  Raw.Lam (sourceName -> x) ann i t -> do
    a <- case ann of
      Just ann' -> check cxt ann' VU
      Nothing   -> freshMeta cxt VU
    va <- eval (cxt^.vals) a
    let cxt' = bind x NOSource va cxt
    (t', liftVal cxt -> b) <- insert cxt' $ infer cxt' t
    pure (Lam x i a t', VPi x i va b)

  Raw.Hole -> do
    a <- freshMeta cxt VU
    ~va <- eval (cxt^.vals) a
    t <- freshMeta cxt va
    pure (t, va)

  Raw.Let (sourceName -> x) a0 t0 u -> do
    a <- check cxt a0 VU
    va <- eval (cxt^.vals) a
    t <- check cxt t0 va
    vt <- eval (cxt^.vals) t
    (u', b) <- infer (define x va vt cxt) u
    pure (Let x a t u', b)

metaName :: Meta -> Name
metaName (MetaRef u _) = MetaName u 0

check :: Context -> Raw.Term -> VTy -> IO TM
check cxt topT ~topA0 = force topA0 >>= \ ftopA -> case (topT, ftopA) of
  (Raw.Loc p t, a) -> addSourcePos p (check cxt t a)

  (Raw.Lam (sourceName -> x) ann0 i t0, VPi _ i' a b) | i == i' -> do
    ann' <- case ann0 of
      Just ann1 -> do
        ann <- check cxt ann1 VU
        ann' <- unsafeInterleaveIO $ eval (cxt^.vals) ann
        unifyWhile cxt ann' a
        pure ann
      Nothing -> uneval (cxt^.len) a
    t <- do
      ty <- b (VVar (cxt^.len))
      check (bind x NOSource a cxt) t0 ty
    pure $ Lam x i ann' t

  (t0, VPi x Implicit a b) -> do
    ty <- b (VVar (cxt^.len))
    t <- check (bind x NOInserted a cxt) t0 ty
    a' <- uneval (cxt^.len) a
    pure $ Lam x Implicit a' t

  -- inserting a new curried function lambda
  (t0, VNe (HMeta _) _) -> do
    -- x <- ("Γ"++) . show <$> readMeta nextMId
    (m,d) <- freshMeta' cxt VTel
    let x = metaName m
    vdom <- unsafeInterleaveIO $ eval (cxt^.vals) d
    let cxt' = bind x NOInserted (VRec vdom) cxt
    (t, liftVal cxt -> a) <- insert cxt' $ infer cxt' t0
    newConstancy cxt vdom a
    unifyWhile cxt topA0 (VPiTel x vdom a)
    pure $ LamTel x d t

  (Raw.Let (sourceName -> x) a0 t0 u0, topA) -> do
    a <- check cxt a0 VU
    va <- unsafeInterleaveIO (eval (cxt^.vals) a)
    t <- check cxt t0 va
    vt <- unsafeInterleaveIO (eval (cxt^.vals) t)
    u <- check (define x va vt cxt) u0 topA
    pure $ Let x a t u

  (Raw.Hole, topA) -> freshMeta cxt topA

  (t0, topA) -> do
    (t, va) <- insert cxt $ infer cxt t0
    unifyWhile cxt va topA
    pure t

