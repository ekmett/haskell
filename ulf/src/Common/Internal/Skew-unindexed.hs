{-# Language BangPatterns #-}
{-# Language RoleAnnotations #-}
{-# Language PatternSynonyms #-}
{-# Language DeriveTraversable #-}
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

import Data.Bits (unsafeShiftR)
import Data.Foldable as Foldable
import Data.Kind

type Tree :: Type -> Type
type role Tree representational
data Tree a 
  = TTip a
  | TBin a !(Tree a) !(Tree a)
  deriving (Functor, Foldable, Traversable)

type Skew :: Type -> Type
type role Skew representational
data Skew a 
  = Nil
  | ConsTree {-# unpack #-} !Int {-# unpack #-} !Int !(Tree a) !(Skew a)
  deriving (Functor, Traversable)

instance Foldable Skew where
  foldMap _ Nil = mempty
  foldMap f (ConsTree _ _ t xs) = foldMap f t <> foldMap f xs
  length Nil = 0
  length (ConsTree n _ _ _) = n
  null Nil = True
  null _ = False

instance Show a => Show (Skew a) where
  showsPrec d = showsPrec d . Foldable.toList

type ViewSkew :: Type -> Type
type role ViewSkew representational
data ViewSkew a where
  ViewNil :: ViewSkew a
  ViewCons :: a -> Skew a -> ViewSkew a

skewCons :: a -> Skew a -> Skew a
skewCons a (ConsTree s n l (ConsTree _ m r xs))
  | n == m = ConsTree (1+s) (2*n+1) (TBin a l r) xs
skewCons a xs = ConsTree (1+length xs) 1 (TTip a) xs

viewSkew :: Skew a -> ViewSkew a
viewSkew Nil = ViewNil
viewSkew (ConsTree _ _ (TTip a) xs) = ViewCons a xs
viewSkew (ConsTree s n (TBin a l r) xs) = ViewCons a $ ConsTree (s-1) n' l $ ConsTree (s-1-n') n' r xs
  where n' = unsafeShiftR n 1

pattern (:*) :: a -> Skew a -> Skew a
pattern v :* e <- (viewSkew -> ViewCons v e) where
  v :* e = skewCons v e

infixr 5 :*
{-# complete Nil, (:*) #-}

lookupSkew :: Skew a -> Int -> a
lookupSkew Nil _ = error "impossible name"
lookupSkew (ConsTree _ n0 t xs) !m0
  | n0 <= m0 = lookupSkew xs (m0 - n0)
  | otherwise = go n0 t m0
  where
    go :: Int -> Tree a -> Int -> a
    go _ (TTip a) _ = a
    go n (TBin a l r) m
      | n == 0 = a
      | m <= n' = go n' l (m - 1)
      | otherwise     = go n' r (m - n' - 1)
      where n' = unsafeShiftR n 1
