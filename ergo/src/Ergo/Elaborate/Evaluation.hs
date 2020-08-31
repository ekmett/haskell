{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language ScopedTypeVariables #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

-- QLF.Elaborate.Evaluation

module Ergo.Elaborate.Evaluation where

import Data.Functor ((<&>))
import Ergo.Elaborate.Monad
import Ergo.Elaborate.Term
import Ergo.Elaborate.Value
import Ergo.Icit
import Ergo.Names

valsLen :: Vals s -> Int
valsLen = go 0 where
  go acc VNil        = acc
  go acc (VDef vs _) = go (acc + 1) vs
  go acc (VSkip vs)  = go (acc + 1) vs

-- eval

evalProj1 :: Val s -> M s (Val s)
evalProj1 (VTcons t _) = pure t
evalProj1 (VNe h sp) = pure $ VNe h (SProj1 sp)
evalProj1 (VLamTel x a t) = evalLamTel pure x a t >>= evalProj1
evalProj1 _ = panic

evalProj2 :: Val s -> M s (Val s)
evalProj2 (VTcons _ u) = pure u
evalProj2 (VNe h sp) = pure $ VNe h (SProj2 sp)
evalProj2 (VLamTel x a t) = evalLamTel pure x a t >>= evalProj2
evalProj2 _ = panic

evalVar :: Ix -> Vals s -> Val s
evalVar 0 (VDef _ v) = v
evalVar 0 (VSkip vs) = VVar (valsLen vs)
evalVar x (VDef vs _) = evalVar (x - 1) vs
evalVar x (VSkip vs) = evalVar (x - 1) vs
evalVar _ _ = panic

evalMeta :: Meta s -> M s (Val s)
evalMeta m = readMeta m <&> \case
  Unsolved{} -> VMeta m
  Solved v -> v
  _ -> panic

evalPiTel :: EVal s -> Name -> VTy s -> EVal s -> M s (Val s)
evalPiTel k x a0 b = force a0 >>= \case
  VTNil -> b VTnil >>= k
  VTCons _ a as -> pure
    let x' = x ++ "1"
        x'' = x ++ "2"
    in VPi x' Implicit a \ ~x1 -> do
      ~x1v <- as x1
      evalPiTel pure x'' x1v \ ~x2 -> b (VTcons x1 x2)
  a -> pure $ VPiTel x a b

evalLamTel :: EVal s -> Name -> VTy s -> EVal s -> M s (Val s)
evalLamTel k x a0 t = force a0 >>= \case
  VTNil -> t VTnil >>= k
  VTCons _ a as -> pure
    let x' = x ++ "1"
        x'' = x ++ "2"
    in VLam x' Implicit a \ ~x1 -> do
      ~x1v <- as x1
      evalLamTel pure x'' x1v \ ~x2 -> t (VTcons x1 x2)
  a -> pure $ VLamTel x a t

evalAppTel ::  VTy s -> Val s -> Val s -> M s (Val s)
evalAppTel a0 t u = force a0 >>= \case
  VTNil -> pure t
  VTCons _ _ as -> do
    u1 <- evalProj1 u
    u1v <- as u1
    u2 <- evalProj2 u
    t' <- evalApp Implicit t u1
    evalAppTel u1v t' u2
  a -> case t of
    VNe h sp -> pure $ VNe h (SAppTel a sp u)
    VLamTel _ _ t' -> t' u
    _ -> panic

evalApp :: Icit -> Val s -> Val s -> M s (Val s)
evalApp _ (VLam _ _ _ t)  u = t u
evalApp i (VNe h sp)      u = pure $ VNe h (SApp i sp u)
evalApp i (VLamTel x a t) u = do
  y <- evalLamTel pure x a t
  evalApp i y u
evalApp _                _ _ = panic

evalAppSp :: forall s. Val s -> Spine s -> M s (Val s)
evalAppSp h = go where
  go SNil             = pure h
  go (SApp i sp u)    = do sp' <- go sp; evalApp i sp' u
  go (SAppTel a sp u) = do sp' <- go sp; evalAppTel a sp' u
  go (SProj1 sp)      = go sp >>= evalProj1
  go (SProj2 sp)      = go sp >>= evalProj2

force :: Val s -> M s (Val s)
force = \case
  v0@(VNe (HMeta m) sp) -> readMeta m >>= \case
    Unsolved{} -> pure v0
    Solved v   -> evalAppSp v sp >>= force
    _ -> panic
  VPiTel x a b -> evalPiTel force x a b
  VLamTel x a t -> evalLamTel force x a t
  v -> pure v

forceSp :: Spine s -> M s (Spine s)
forceSp sp =
  -- This is a cheeky hack, the point is that (VVar (-1)) blocks computation, and
  -- we get back the new spine.  We use (-1) in order to make the hack clear in
  -- potential debugging situations.
  evalAppSp (VVar (-1)) sp >>= \case
    VNe _ sp' -> pure sp'
    _ -> panic

eval :: Vals s -> Tm (Meta s) -> M s (Val s)
eval vs = go where
  go = \case
    Var x        -> pure $ evalVar x vs
    Let _ _ t u  -> go t >>= goBind u
    U            -> pure VU
    Meta m       -> evalMeta m
    Pi x i a b   -> unsafeInterleaveM (go a) <&> \a' -> VPi x i a' (goBind b)
    Lam x i a t  -> unsafeInterleaveM (go a) <&> \a' -> VLam x i a' (goBind t)
    App i t u    -> do
      t' <- unsafeInterleaveM (go t)
      u' <- unsafeInterleaveM (go u)
      evalApp i t' u'
    Tel          -> pure VTel
    TNil         -> pure VTNil
    TCons x a b  -> unsafeInterleaveM (go a) <&> \a' -> VTCons x a' (goBind b)
    Rec a        -> VRec <$> go a
    Tnil         -> pure VTnil
    Tcons t u    -> VTcons <$> unsafeInterleaveM (go t) <*> unsafeInterleaveM (go u)
    Proj1 t      -> go t >>= evalProj1
    Proj2 t      -> go t >>= evalProj2
    PiTel x a b  -> do
      a' <- unsafeInterleaveM (go a)
      evalPiTel pure x a' (goBind b)
    AppTel a t u -> do
      a' <- unsafeInterleaveM (go a)
      t' <- unsafeInterleaveM (go t)
      u' <- unsafeInterleaveM (go u)
      evalAppTel a' t' u'
    LamTel x a t -> do
      a' <- unsafeInterleaveM (go a)
      evalLamTel pure x a' (goBind t)
    Skip t -> eval (VSkip vs) t

  goBind t x = eval (VDef vs x) t

uneval :: Lvl -> Val s -> M s (Tm (Meta s))
uneval d = go where
  go v = force v >>= \case
    VNe h sp0 ->
      let goSp SNil = case h of
            HMeta m -> pure $ Meta m
            HVar x  -> pure $ Var (d - x - 1)
          goSp (SApp i sp u) = App i <$> goSp sp <*> go u
          goSp (SAppTel a sp u) = AppTel <$> go a <*> goSp sp <*> go u
          goSp (SProj1 sp) = Proj1 <$> goSp sp
          goSp (SProj2 sp) = Proj2 <$> goSp sp
      in forceSp sp0 >>= goSp

    VLam x i a t  -> Lam x i <$> go a <*> goBind t
    VPi x i a b   -> Pi x i <$> go a <*> goBind b
    VU            -> pure U
    VTel          -> pure Tel
    VRec a        -> Rec <$> go a
    VTNil         -> pure TNil
    VTCons x a as -> TCons x <$> go a <*> goBind as
    VTnil         -> pure Tnil
    VTcons t u    -> Tcons <$> go t <*> go u
    VPiTel x a b  -> PiTel x <$> go a <*> goBind b
    VLamTel x a t -> LamTel x <$> go a <*> goBind t

  goBind t = t (VVar d) >>= uneval (d + 1)

nf :: Vals s -> Tm (Meta s) -> M s (Tm (Meta s))
nf vs t = do
  v <- eval vs t
  uneval 0 v
{-# inline nf #-}

