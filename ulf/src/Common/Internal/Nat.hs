{-# Language ScopedTypeVariables #-}
{-# Language PatternSynonyms #-}
{-# Language DerivingStrategies #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language StandaloneKindSignatures #-}
{-# Language ViewPatterns #-}
{-# Language RoleAnnotations #-}
{-# Language GADTs #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language RankNTypes #-}

module Common.Internal.Nat
  ( ToInt(..)
  , type Z
  , type S
  , wk
  , wk2
  , N(UnsafeN,NZ,NS)
  , ViewN(..)
  , Fin(UnsafeFin,Z,S)
  ) where

import Data.Kind
import Data.Type.Equality
import GHC.TypeNats
import Unsafe.Coerce

class ToInt t where
  int :: t -> Int

instance ToInt Int where
  int = id

type Z = 0
type S n = 1 + n

wk :: forall i r proxy. proxy i -> (i <= S i => r) -> r
wk _ r = case unsafeCoerce Refl of
  (Refl :: (i <=? S i) :~: 'True) -> r

wk2 :: forall j i r p q. j <= i => p i -> q j -> (j <= S i => r) -> r
wk2 _ _ r = case unsafeCoerce Refl of
  (Refl :: (j <=? S i) :~: 'True) -> r

type N :: Nat -> Type
type role N nominal
newtype N i = UnsafeN Int
  deriving newtype (ToInt, Show)

type ViewN :: Nat -> Type
type role ViewN nominal
data ViewN n where
  ViewNZ :: ViewN Z
  ViewNS :: N n -> ViewN (S n)

viewNat :: N n -> ViewN n
viewNat (UnsafeN 0) = unsafeCoerce ViewNZ
viewNat (UnsafeN n) = unsafeCoerce (ViewNS $ UnsafeN (n-1))

pattern NZ :: () => (n ~ Z) => N n
pattern NZ <- (viewNat -> ViewNZ) where
  NZ = UnsafeN 0

pattern NS :: () => (n ~ S n') => N n' -> N n
pattern NS n <- (viewNat -> ViewNS n) where
  NS n = UnsafeN (int n + 1)

{-# complete NZ, NS #-}

-------------------------------------------------------------------------------
-- * Fin n
-------------------------------------------------------------------------------

type ViewFin :: Nat -> Type
type role ViewFin nominal
data ViewFin j where
  ViewZ :: ViewFin (S j)
  ViewS :: Fin j -> ViewFin (S j) -- Fin (S j) -> ViewFin (S (S j)) ?

type Fin :: Nat -> Type
type role Fin nominal
newtype Fin j = UnsafeFin Int
instance ToInt (Fin j) where int (UnsafeFin n) = n

instance Show (Fin j) where
  showsPrec d = showsPrec d . int

viewFin :: Fin i -> ViewFin i
viewFin (UnsafeFin 0) = unsafeCoerce ViewZ
viewFin (UnsafeFin n) = unsafeCoerce (ViewS $ UnsafeFin (n-1))

pattern Z :: Fin (S j)
pattern Z <- (viewFin -> ViewZ) where
  Z = UnsafeFin 0

pattern S :: () => (j ~ S i) => Fin i -> Fin j
pattern S n <- (viewFin -> ViewS n) where
  S n = UnsafeFin (int n + 1)

{-# complete Z, S #-}
