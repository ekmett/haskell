{-# Language DataKinds #-}
{-# Language BangPatterns #-}
{-# Language ConstraintKinds #-}
{-# Language QuantifiedConstraints #-}
{-# Language KindSignatures #-}
{-# Language GADTs #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
module Nat 
  ( Valued(..)
  , Nat(..)
  , SNat(..)
  , KnownNat(..)
  , Fin(..)
  , type (+)
  , addFin
  ) where

--------------------------------------------------------------------------------
-- * Valued
--------------------------------------------------------------------------------

class Valued t where
  value :: t -> Int

--------------------------------------------------------------------------------
-- * Nat
--------------------------------------------------------------------------------

data Nat = Z | S !Nat
  deriving (Eq,Ord)

instance Show Nat where
  showsPrec d = showsPrec d . value

instance Valued Nat where
  value = go 0 where
    go !n Z = n
    go n (S m) = go (1 + n) m

--------------------------------------------------------------------------------
-- * SNat
--------------------------------------------------------------------------------

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

instance Valued (SNat n) where
  value n0 = go 0 n0 where
    go :: Int -> SNat n -> Int
    go !n SZ = n
    go n (SS m) = go (1 + n) m

instance Show (SNat n) where
  showsPrec d = showsPrec d . value

--------------------------------------------------------------------------------
-- * KnownNat
--------------------------------------------------------------------------------

class KnownNat (t :: Nat) where
  snat :: SNat t

instance KnownNat Z where
  snat = SZ

instance KnownNat n => KnownNat (S n) where
  snat = SS snat

--------------------------------------------------------------------------------
-- * Grades
--------------------------------------------------------------------------------

class Graded t where
  grade :: t n -> SNat n

instance Graded SNat where
  grade = id

--------------------------------------------------------------------------------
-- * Fin
--------------------------------------------------------------------------------

data Fin (n :: Nat) where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

instance Valued (Fin n) where
  value = go 0 where
    go :: Int -> Fin n -> Int
    go !n FZ = n
    go n (FS m) = go (1 + n) m

instance Show (Fin n) where
  showsPrec d = showsPrec d . value

type family (n :: Nat) + (m :: Nat) :: Nat where
  Z + m = m 
  S n + m = S (n + m)

infixl 6 +

addFin :: SNat n -> Fin m -> Fin (n + m)
addFin SZ m = m
addFin (SS n) m = FS (addFin n m)
