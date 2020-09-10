{-# Language BangPatterns #-}
{-# Language RoleAnnotations #-}
{-# Language PatternSynonyms #-}
{-# Language ViewPatterns #-}
{-# Language StandaloneKindSignatures #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}

module Common.Internal.Skew 
  ( Tree(..)
  , Skew(.., (:*))
  , ViewSkew(..)
  , viewSkew
  , lookupSkew
  ) where

import Common.Internal.Nat
import GHC.TypeNats
import Data.Bits (unsafeShiftR)
import Data.Kind

type Tree :: Nat -> Nat -> Type -> Type
type role Tree nominal nominal representational
data Tree j k a where
  TTip :: a -> Tree (S i) i a
  TBin :: a -> !(Tree i j a) -> !(Tree j k a) -> Tree (S i) k a

instance Functor (Tree j k) where
  fmap f (TTip a) = TTip (f a)
  fmap f (TBin a l r) = TBin (f a) (fmap f l) (fmap f r)

instance Foldable (Tree j k) where
  foldMap f (TTip a) = f a
  foldMap f (TBin a l r) = f a <> foldMap f l <> foldMap f r

instance Traversable (Tree j k) where
  traverse f (TTip a) = TTip <$> f a
  traverse f (TBin a l r) = TBin <$> f a <*> traverse f l <*> traverse f r

type Skew :: Nat -> Type -> Type
type role Skew nominal representational
data Skew i a where
  ConsTree :: {-# unpack #-} !Int -> !(Tree i j a) -> !(Skew j a) -> Skew i a
  Nil  :: Skew Z a

instance Functor (Skew i) where
  fmap _ Nil = Nil
  fmap f (ConsTree i t xs) = ConsTree i (fmap f t) (fmap f xs)

instance Foldable (Skew i) where
  foldMap _ Nil = mempty
  foldMap f (ConsTree _ t xs) = foldMap f t <> foldMap f xs

instance Traversable (Skew i) where
  traverse _ Nil = pure Nil
  traverse f (ConsTree i t xs) = ConsTree i <$> traverse f t <*> traverse f xs

type ViewSkew :: Nat -> Type -> Type
type role ViewSkew nominal representational
data ViewSkew i a where
  ViewNil :: ViewSkew Z a
  ViewCons :: a -> Skew i a -> ViewSkew (S i) a

skewCons :: a -> Skew i a -> Skew (S i) a
skewCons a (ConsTree n l (ConsTree m r xs))
  | n == m = ConsTree (2*n+1) (TBin a l r) xs
skewCons a xs = ConsTree 1 (TTip a) xs

viewSkew :: Skew i a -> ViewSkew i a
viewSkew Nil = ViewNil
viewSkew (ConsTree _ (TTip a) xs)     = ViewCons a xs
viewSkew (ConsTree n (TBin a l r) xs) = ViewCons a $ ConsTree n' l $ ConsTree n' r xs
  where n' = unsafeShiftR n 1

pattern (:*) :: () => (l ~ S k) => a -> Skew k a -> Skew l a
pattern v :* e <- (viewSkew -> ViewCons v e) where
  v :* e = skewCons v e

infixr 5 :*
{-# complete Nil, (:*) #-}

lookupSkew :: Skew i a -> Fin i -> a
lookupSkew Nil _ = error "impossible name"
lookupSkew (ConsTree n0 t xs) !m0
  | n0 <= int m0 = lookupSkew xs (UnsafeFin (int m0 - n0))
  | otherwise = go n0 t m0
  where
    go :: Int -> Tree j k a -> Fin j -> a
    go _ (TTip a) _ = a
    go n (TBin a l r) m
      | n == 0 = a
      | int m <= n' = go n' l $ UnsafeFin (int m - 1)
      | otherwise     = go n' r $ UnsafeFin (int m - n' - 1)
      where n' = unsafeShiftR n 1

