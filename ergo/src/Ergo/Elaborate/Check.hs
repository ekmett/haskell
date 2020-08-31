{-# Language ImportQualifiedPost #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Check where

import Data.HashSet qualified as HS
import Ergo.Elaborate.Value

data Occurs s
  = Rigid          -- ^ At least one occurrence is not in the spine of any meta.
  | Flex (Metas s) -- ^ All occurrences are inside spines of metas. We store the set of such metas.
  | None           -- ^ The variable does not occur.
  deriving Eq

instance Semigroup (Occurs s) where
  Flex ms <> Flex ms' = Flex (ms <> ms')
  Rigid   <> _        = Rigid
  _       <> Rigid    = Rigid
  None    <> r        = r
  l       <> None     = l

instance Monoid (Occurs s) where
  mempty = None

occurrence :: Metas s -> Occurs s
occurrence ms
  | HS.null ms = Rigid
  | otherwise = Flex ms


{-

infer :: Context s -> Raw.Term -> M s (Tm (Meta RealWorld), VTy s)
infer cxt = \case
  Raw.U -> pure (U, VU)

  Raw.Var x -> do
    let go :: [Name] -> [NameOrigin] -> Types -> Int -> ST s (Tm s, VTy s)
        go (y:xs) (NOSource:os) (TSnoc _ a) i | x == y || ('*':x) == y = pure (Var i,a)
        go (_:xs) (_:os) (TSnoc as _) i = go xs os as (i + 1)
        go [] [] TNil _ = report (cxt^.names) (NameNotInScope x)
        go _ _ _ _ = panic
    go (cxt^.names) (cxt^.nameOrigin) (cxt^.types) 0

  Raw.Pi x i a b -> do
    a <- check cxt a VU
    eval (cxt^.vals) a
    b <- check (bind x NOSource va cxt) b VU
    pure (Pi x i a b, VU)

  Raw.App i t u -> do
    (t, va) <- case i of 
      Explicit -> insert' cxt $ infer cxt t
      _ -> infer cxt t
    force va >>= \case
      VPi x i' a b -> do
        unless (i == i') $
          err (cxt^.names) $ IcitMismatch i i'
        u <- check cxt u a
        pure (App t u i, b (eval (cxt^.vals) u))
      VNe (HMeta m) sp -> do
        a <- eval (cxt^.vals) <$> freshMeta cxt VU
        cod  <- freshMeta (bind "x" NOInserted a cxt) VU
        let b ~x = eval (VDef (cxt^.vals) x) cod
        unifyWhile cxt (VNe (HMeta m) sp) (VPi "x" i a b)
        u' <- check cxt u a
        ty <- b (eval (cxt^.vals) u')
        pure (App t u' i, ty)
      _ -> err (cxt^.names) $ ExpectedFunction (quote (cxt^.len) va)

  Raw.Lam x ann i t -> do
    a <- case ann of
      Just ann -> check cxt ann VU
      Nothing  -> freshMeta cxt VU
    va <- eval (cxt^.vals) a
    let cxt' = bind x NOSource va cxt
    (t, liftVal cxt -> b) <- insert cxt' $ infer cxt' t
    pure (Lam x i a t, VPi x i va b)

  Raw.Hole -> do
    a <- freshMeta cxt VU
    ~va <- eval (cxt^.vals) a
    t <- freshMeta cxt va
    pure (t, va)

  Raw.Let x a t u -> do
    a <- check cxt a VU
    ~va <- eval (cxt^.vals) a
    t <- check cxt t va
    ~vt <- eval (cxt^.vals) t
    (u, b) <- infer (define x va vt cxt) u
    pure (Let x a t u, b)

-}
