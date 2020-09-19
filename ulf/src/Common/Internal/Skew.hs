{-# Language BangPatterns #-}
{-# Language RoleAnnotations #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
{-# Language RankNTypes #-}
{-# Language TypeOperators #-}
{-# Language StandaloneKindSignatures #-}
{-# Language ScopedTypeVariables #-}
{-# Language DataKinds #-}
{-# Language ConstraintKinds #-}
{-# Language GADTs #-}

module Common.Internal.Skew 
{-
  ( Tree(..)
  , Skew(.., (:*))
  , ViewSkew(..)
  , viewSkew
  , lookupSkew
  , sizeSkew
  )-} where

import Common.Internal.Nat
import Common.Ix
import GHC.TypeNats
import Data.Bits (unsafeShiftR)
import Data.Kind
import Data.Type.Equality
import Unsafe.Coerce

data List f i where
  Cons :: f i -> List f i -> List f (1 + i)
  Nil  :: List f 0

lookupList :: Wk i j -> List f j -> f i
lookupList 
lookupSkew :: forall f i. Weak f => Skew f i -> Ix i -> (forall j. j :<= i -> f j -> r) -> r


{-
type Tree :: Nat -> Nat -> (Nat -> Type) -> Type
type role Tree nominal nominal nominal
data Tree j k f where
  TTip :: f i -> Tree (S i) i f
  TBin :: (i ~ S i', j ~ S j') => f i -> !(Tree i j f) -> !(Tree j k f) -> Tree (S i) k f

type Skew :: (Nat -> Type) -> Nat -> Type
type role Skew nominal nominal
data Skew f i where
  ConsTree :: {-# unpack #-} !(N (S i)) -> {-# unpack #-} !Int -> !(Tree (S i) j f) -> !(Skew f j) -> Skew f (S i)
  Nil      :: Skew f Z

sizeSkew :: Skew f i -> N i
sizeSkew Nil = NZ
sizeSkew (ConsTree n _ _ _) = n

type ViewSkew :: (Nat -> Type) -> Nat -> Type
type role ViewSkew nominal nominal
data ViewSkew f i where
  ViewCons :: f i -> Skew f i -> ViewSkew f (S i)
  ViewNil  :: ViewSkew f Z

skewCons :: f i -> Skew f i -> Skew f (S i)
skewCons a (ConsTree s n l (ConsTree _ m r xs))
  | n == m = ConsTree (NS s) (2*n+1) (TBin a l r) xs
skewCons a xs = ConsTree (NS (sizeSkew xs)) 1 (TTip a) xs

viewSkew :: Skew f i -> ViewSkew f i
viewSkew Nil = ViewNil
viewSkew (ConsTree _ _ (TTip a) xs) = ViewCons a xs
viewSkew (ConsTree s n (TBin a l r) xs) 
  = ViewCons a $ ConsTree (UnsafeN (int s-1)) n' l $ ConsTree (UnsafeN $ int s-int n'-1) n' r xs
  where n' = unsafeShiftR n 1

pattern (:*) :: () => (j ~ S i) => f i -> Skew f i -> Skew f j
pattern v :* e <- (viewSkew -> ViewCons v e) where
  v :* e = skewCons v e

infixr 5 :*
{-# complete Nil, (:*) #-}

-- newtype Wk f g i = Wk (forall j. j <= i => f j -> f i)

class Weak f where
  weaken :: i <= j => f i -> f j
  weaken = unsafeWeaken

  unsafeWeaken :: forall i j. f i -> f j
  unsafeWeaken = case unsafeCoerce (Refl :: (i <=? i) :~: 'True) of
    (Refl :: (i <=? j) :~: 'True) -> weaken
  {-# MINIMAL weaken | unsafeWeaken #-}

-- i <= j -- constructively witnessed
newtype i :<= j = UnsafeWk Int

instance Category (Wk i j) where
  id = UnsafeWk 0
  UnsafeWk a . UnsafeWk b = UnsafeWk (a + b)

lookupSkew :: forall f i. Weak f => Skew f i -> Ix i -> (forall j. j :<= i -> f j -> r) -> r
lookupSkew Nil _ _ = error "impossible name"
lookupSkew (ConsTree _ n0 t xs) !m0 φ 
  | n0 <= int m0 = unsafeWeaken $ lookupSkew xs (UnsafeFin (int m0 - n0))
  | otherwise = go n0 t m0
  where
    go :: Int -> Tree j k f -> Fin j -> f i
    go _ (TTip a) _ = unsafeWeaken a
    go n (TBin a l r) m
      | n == 0 = unsafeWeaken a
      | int m <= n'   = go n' l $ UnsafeFin (int m - 1)
      | otherwise     = go n' r $ UnsafeFin (int m - n' - 1)
      where n' = unsafeShiftR n 1
-}
