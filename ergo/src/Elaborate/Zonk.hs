{-# Language ScopedTypeVariables #-}
{-# Language LambdaCase #-}

module Elaborate.Zonk where

import Data.Functor ((<&>))
import Elaborate.Evaluation
import Elaborate.Term
import Elaborate.Value
import Elaborate.Monad

-- | Unfold all metas and evaluate meta-headed spines, but don't evaluate
--   anything else.
zonk :: forall s. Vals s -> TM s -> M s (TM s)
zonk vs t0 = go t0 where

  goSp :: TM s -> M s (Either (Val s) (TM s))
  goSp = \case
    Meta m -> readMeta m <&> \case
      Solved v -> Left v
      _        -> Right (Meta m)
    App ni t1 u -> goSp t1 >>= \case
      Left t  -> Left <$> do
        u' <- eval vs u
        evalApp ni t u'
      Right t -> go u <&> \u' -> Right $ App ni t u'
    AppTel a t1 u -> goSp t1 >>= \case
      Left t  -> do
        a' <- eval vs a
        u' <- eval vs u
        Left <$> evalAppTel a' t u'
      Right t -> do
        a' <- go a 
        u' <- go u
        pure $ Right $ AppTel a' t u'
    t -> Right <$> zonk vs t

  goBind = zonk (VSkip vs)

  go = \case
    Var x        -> pure $ Var x
    Meta m       -> readMeta m >>= \case
      Solved v   -> uneval (valsLen vs) v
      Unsolved{} -> pure $ Meta m
      _          -> panic
    U            -> pure U
    Pi x i a b   -> Pi x i <$> go a <*> goBind b
    App ni t1 u   -> goSp t1 >>= \case
      Left t  -> do
        u' <- eval vs u
        t' <- evalApp ni t u'
        uneval (valsLen vs) t'
      Right t -> App ni t <$> go u
    Lam x i a t  -> Lam x i <$> go a <*> goBind t
    Let x a t u  -> Let x <$> go a <*> go t <*> goBind u
    Tel          -> pure Tel
    TNil         -> pure TNil
    TCons x t u  -> TCons x <$> go t <*> goBind u
    Rec a        -> Rec <$> go a
    Tnil         -> pure Tnil
    Tcons t u    -> Tcons <$> go t <*> go u
    Proj1 t      -> Proj1 <$> go t
    Proj2 t      -> Proj2 <$> go t
    PiTel x a b  -> PiTel x <$> go a <*> goBind b
    AppTel a t1 u -> goSp t1 >>= \case
      Left t  -> do
        a' <- eval vs a
        u' <- eval vs u
        t' <- evalAppTel a' t u'
        uneval (valsLen vs) t'
      Right t -> do
        a' <- go a
        u' <- go u
        pure $ AppTel a' t u'
    LamTel x a b -> LamTel x <$> go a <*> goBind b
    Skip t       -> Skip <$> goBind t
