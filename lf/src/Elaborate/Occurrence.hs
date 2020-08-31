{-# Language ImportQualifiedPost #-}
{-# Language RankNTypes #-}
{-# Language LambdaCase #-}
{-# Language ScopedTypeVariables #-}

-- |
-- Copyright :  (c) Edward Kmett 2020, András Kovács 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Elaborate.Occurrence 
  ( Occurs(..)
  , occurs
  , occurrence
  ) where


import Control.Applicative (liftA2)
--import Control.Monad.Primitive
--import Control.Monad.ST
import Data.HashSet qualified as HS
import Elaborate.Evaluation
import Elaborate.Monad
import Elaborate.Value

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

(><) :: M s (Occurs s) -> M s (Occurs s) -> M s (Occurs s)
(><) = liftA2 (<>)

-- | Occurs check for the purpose of constancy constraint solving.
occurs :: Lvl -> Lvl -> Val s -> M s (Occurs s)
occurs d0 topX v0 = occurs' d0 mempty v0 where

  occurs' :: Lvl -> Metas s -> Val s -> M s (Occurs s)
  occurs' d ms0 = go where

    goSp ms sp0 = forceSp sp0 >>= \case
      SNil           -> pure mempty
      SApp _ sp u    -> goSp ms sp >< go u
      SAppTel a sp u -> go a >< goSp ms sp >< go u
      SProj1 sp      -> goSp ms sp
      SProj2 sp      -> goSp ms sp

    goBind t = t (VVar d) >>= occurs' (d + 1) ms0

    go v = force v >>= \case
      VNe (HVar x) sp 
        | x == topX -> (occurrence ms0 <>) <$> goSp ms0 sp
        | otherwise -> goSp ms0 sp
      VNe (HMeta m) sp -> goSp (HS.insert m ms0) sp
      VPi _ _ a b   -> go a >< goBind b
      VLam _ _ a t  -> go a >< goBind t
      VU            -> pure mempty
      VTel          -> pure mempty
      VRec a        -> go a
      VTNil         -> pure mempty
      VTCons _ a b  -> go a >< goBind b
      VTnil         -> pure mempty
      VTcons t u    -> go t >< go u
      VPiTel _ a b  -> go a >< goBind b
      VLamTel _ a t -> go a >< goBind t
{-# inline occurs #-}
