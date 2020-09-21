{-# language CPP #-}
{-# Language BlockArguments #-}
{-# Language ImportQualifiedPost #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# language AllowAmbiguousTypes #-}
{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language PatternSynonyms #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneKindSignatures #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language ViewPatterns #-}
{-# language Unsafe #-}
{-# language UndecidableInstances #-}
{-# OPTIONS_HADDOCK not-home #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- #define INJECTIVE_SUCC 1

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Internal where

import Data.Eq.Structural
import Data.Function
import Data.Int
import Data.Kind
import Data.Proxy
import Data.Some
import Data.Type.Equality
import Data.Word
import Foreign.Ptr
import Foreign.StablePtr
import GHC.Exts
import GHC.TypeLits as TL
import GHC.TypeNats as TN
import Numeric.Natural
import Text.Read hiding (Symbol)
import Type.Reflection
import Unsafe.Coerce

--------------------------------------------------------------------------------
-- * Singletons
--------------------------------------------------------------------------------

type Sing :: forall k. k -> Type
newtype Sing (a :: k) = UnsafeSing { fromSing :: k }

instance (Typeable k, Show k) => Show (Sing (a :: k)) where
  showsPrec d (Sing k) = showParen (d > 10) $
    showString "Sing @" . showsPrec 11 (typeRep @k) . showChar ' ' . showsPrec 11 k

pattern Sing :: k -> Sing (a :: k)
pattern Sing x <- (UnsafeSing x)

{-# complete Sing #-}

instance Eq (Sing a) where
  _ == _ = True

instance SEq (Sing a)

instance Ord (Sing a) where
  compare _ _ = EQ

-- assumes equality is structural.
instance SEq k => TestEquality (Sing :: k -> Type) where
  testEquality i j
    | fromSing i == fromSing j = Just (unsafeCoerce Refl)
    | otherwise = Nothing

type SingI :: forall k. k -> Constraint
class SingI (a :: k) where
  sing :: Sing a

type Reifies k (a::k) = SingI a

type Wrap :: forall k. k -> Type -> Type
#ifdef USE_MAGICDICT
data Wrap s r = Wrap (SingI s => Proxy# s -> r)
ify# :: (SingI a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
ify# f x y = magicDict (Wrap f) x y
#else
newtype Wrap s r = Wrap (SingI s => Proxy# s -> r)
ify# :: (SingI a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
ify# f x y = unsafeCoerce (Wrap f) x y
{-# inline ify# #-}
#endif

ify :: Sing a -> (SingI a => r) -> r
ify s r = ify# (\_ -> r) s proxy#

reify :: k -> (forall (a::k). SingI a => Proxy# a -> r) -> r
reify k f = ify# f (UnsafeSing k) proxy#

-- ambiguous types
reflect :: forall k a. Reifies k a => k
reflect = fromSing (sing @k @a)

--------------------------------------------------------------------------------
-- * Lowering Types
--------------------------------------------------------------------------------

type Type' = Some (TypeRep :: Type -> Type)

toType :: Type' -> Type
toType = unsafeCoerce

fromType :: Type -> Type'
fromType = unsafeCoerce

instance Show Type where
  showsPrec d (Type t) = showsPrec d t

pattern Type :: TypeRep (a :: Type) -> Type
pattern Type t <- (fromType -> Some t) where
  Type t = toType (Some t)

instance Typeable a => SingI (a :: Type) where
  sing = UnsafeSing $ Type $ typeRep @a

type SType' :: Type -> Type
data SType' a where
  SType' :: TypeRep a -> SType' (a :: Type)

upSType :: Sing a -> SType' a
upSType (Sing (Type t)) = unsafeCoerce (SType' t)

pattern SType :: TypeRep a -> Sing (a :: Type)
pattern SType t <- (upSType -> SType' t) where
  SType t = UnsafeSing $ Type t

--------------------------------------------------------------------------------
-- * Lowering Nats
--------------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} KnownNat a => SingI a where
  sing = UnsafeSing $ Nat $ TN.natVal (Proxy @a)

instance Show Nat where
  showsPrec d = showsPrec d . fromNat

instance Eq Nat where
  (==) = (==) `on` fromNat

#ifndef INJECTIVE_SUCC
instance SEq Nat
#endif

instance Ord Nat where
  compare = compare `on` fromNat

instance Read Nat where
  readPrec = Nat <$> readPrec

toNat :: Natural -> Nat
toNat = unsafeCoerce

fromNat :: Nat -> Natural
fromNat = unsafeCoerce

liftN2 :: (Natural -> Natural -> Natural) -> Nat -> Nat -> Nat
liftN2 f x y = Nat $ f (fromNat x) (fromNat y)

liftN :: (Natural -> Natural) -> Nat -> Nat
liftN f = Nat . f . fromNat

instance Num Nat where
  (+) = liftN2 (+)
  (-) = liftN2 (-)
  (*) = liftN2 (*)
  abs = liftN abs
  signum = liftN signum
  negate = liftN negate
  fromInteger = Nat . fromInteger

instance Enum Nat where
  succ = liftN succ
  pred = liftN pred
  toEnum = Nat . toEnum
  fromEnum = fromEnum . fromNat
  enumFrom = fmap Nat . enumFrom . fromNat
  enumFromTo (Nat n) (Nat m) = Nat <$> enumFromTo n m
  enumFromThen (Nat n) (Nat m) = Nat <$> enumFromThen n m
  enumFromThenTo (Nat n) (Nat m) (Nat o) = Nat <$> enumFromThenTo n m o

instance Real Nat where
  toRational = toRational . fromNat

instance Integral Nat where
  quot = liftN2 quot
  rem = liftN2 rem
  div = liftN2 rem
  mod = liftN2 rem
  quotRem (Nat n) (Nat m) = case quotRem n m of
    (q,r) -> (Nat q, Nat r)
  divMod (Nat n) (Nat m) = case divMod n m of
    (q,r) -> (Nat q, Nat r)
  toInteger = toInteger . fromNat

pattern Nat :: Natural -> Nat
pattern Nat n <- (fromNat -> n) where
  Nat n = toNat n

{-# complete Nat #-}

-----------------------------------------------------------------------------
-- * Lifting Natural
--
-- Unlike 'Nat' we can provide an injective 'S' here
-- Unfortunately we don't get a nice syntax for huge numeric
-- literals, so uh, don't use this for that. Use 'Nat'.
--
-- When GHC releases a version with 'Nat' = 'Natural', we'll just
-- make our own 'Nat' type.
-----------------------------------------------------------------------------

pattern Z :: Integral a => a
pattern Z = 0

pattern S :: Integral a => a -> a
pattern S n <- ((\case 0 -> Nothing; n -> Just $ n-1) -> Just n)
  where S n = n+1

{-# complete Z, S :: Natural #-}
{-# complete Z, S :: Int #-}
{-# complete Z, S :: Int8 #-}
{-# complete Z, S :: Int16 #-}
{-# complete Z, S :: Int32 #-}
{-# complete Z, S :: Int64 #-}
{-# complete Z, S :: IntPtr #-}
{-# complete Z, S :: Word #-}
{-# complete Z, S :: Word8 #-}
{-# complete Z, S :: Word16 #-}
{-# complete Z, S :: Word32 #-}
{-# complete Z, S :: Word64 #-}
{-# complete Z, S :: WordPtr #-}

data family Z' :: k
data family S' :: k -> k

type Z :: forall k. k
type family Z :: k where
  Z = 0
  Z = Z''

type S :: forall k. k -> k
type family S (n::k) :: k where
  S n = 1 + n
  S n = S'' n

type SIntegral' :: forall k. k -> Type
data SIntegral' (n :: k) where
  SZ' :: SIntegral' Z'
  SS' :: Sing (n :: k) -> SIntegral' (S' n :: k)

upSIntegral :: forall k (n::k). Nice k => Sing n -> SIntegral' n
upSIntegral (UnsafeSing 0) = unsafeCoerce SZ'
upSIntegral (UnsafeSing n) = unsafeCoerce $ SS' (UnsafeSing (n-1))

class Integral a => Nice a where
  type Z'' :: a
  type Z'' = Z'

  type S'' :: a -> a
  type S'' = S'

instance Nice Natural -- When GHC makes 'Natural' = 'Nat' this will not be 'Nice'
instance Nice Int
instance Nice Int8
instance Nice Int16
instance Nice Int32
instance Nice Int64
instance Nice IntPtr
instance Nice Word
instance Nice Word8
instance Nice Word16
instance Nice Word32
instance Nice Word64
instance Nice WordPtr
instance Nice Integer -- Not everything can be reached by @S@, the complete pragma lies

-- instance Nice Nat -- 'Nat' is not 'Nice'.

pattern SZ
  :: forall k (n::k). Nice k
  => n ~ Z' => Sing n
pattern SZ <- (upSIntegral -> SZ') where
  SZ = UnsafeSing 0

pattern SS
  :: forall k (n::k). Nice k
  => forall (n'::k). n ~ S' n'
  => Sing n' -> Sing n
pattern SS n <- (upSIntegral -> SS' n) where
  SS (Sing n) = UnsafeSing $ S n

{-# complete SS, SZ #-}

instance forall k (a::k). (Nice k, SingI a) => SingI (S' a) where
  sing = SS sing

instance Nice k => SingI (Z'::k) where
  sing = SZ

--------------------------------------------------------------------------------
-- * Lifting (Ptr a)
--------------------------------------------------------------------------------

data family FromWordPtr :: WordPtr -> k

type MkPtr :: forall a. WordPtr -> Ptr a
type MkPtr = FromWordPtr

instance SingI n => SingI (MkPtr n) where
  sing = SMkPtr sing

pattern SMkPtr :: Sing n -> Sing (MkPtr n)
pattern SMkPtr n <- Sing (UnsafeSing . ptrToWordPtr -> n) where
  SMkPtr (Sing n) = UnsafeSing $ wordPtrToPtr n

{-# complete SMkPtr #-}

--------------------------------------------------------------------------------
-- * Lifting (StablePtr a)
--------------------------------------------------------------------------------

data family FromPtr :: Ptr a -> k

type MkStablePtr :: forall a. Ptr () -> StablePtr a
type MkStablePtr = FromPtr

instance SingI n => SingI (MkStablePtr n) where
  sing = SMkStablePtr sing

pattern SMkStablePtr :: Sing n -> Sing (MkStablePtr n)
pattern SMkStablePtr n <- Sing (UnsafeSing . castStablePtrToPtr -> n) where
  SMkStablePtr (Sing n) = UnsafeSing $ castPtrToStablePtr n

{-# complete SMkStablePtr #-}

--------------------------------------------------------------------------------
-- * Lifting Char
--------------------------------------------------------------------------------

data family FromSymbol :: Symbol -> k

type MkChar :: Symbol -> Char
type MkChar = FromSymbol

instance KnownSymbol s => SingI (MkChar s) where
  sing = case symbolVal $ Proxy @s of
    [c] -> UnsafeSing c
    _ -> error "SChar.sing: bad argument"

--------------------------------------------------------------------------------
-- * Lowering Symbol
--------------------------------------------------------------------------------

toSymbol :: String -> Symbol
toSymbol = unsafeCoerce

fromSymbol :: Symbol -> String
fromSymbol = unsafeCoerce

pattern Symbol :: String -> Symbol
pattern Symbol s <- (fromSymbol -> s) where
  Symbol s = toSymbol s

{-# complete Symbol #-}

instance Eq Symbol where
  (==) = (==) `on` fromSymbol

instance Ord Symbol where
  compare = compare `on` fromSymbol

instance Show Symbol where
  showsPrec d = showsPrec d . fromSymbol

instance Read Symbol where
  readPrec = Symbol <$> readPrec

instance IsList Symbol where
  type Item Symbol = Char
  fromList = Symbol . fromList
  fromListN n xs = Symbol (fromListN n xs)
  toList = toList . fromSymbol

instance IsString Symbol where
  fromString = toSymbol

instance KnownSymbol s => SingI s where
  sing = UnsafeSing $ Symbol $ symbolVal $ Proxy @s

--------------------------------------------------------------------------------
-- * Singleton Lists
--------------------------------------------------------------------------------

type SList' :: forall a. [a] -> Type
type role SList' nominal
data SList' a where
  SNil' :: SList' '[]
  SCons' :: Sing a -> Sing as -> SList' (a ': as)

upSList :: Sing a -> SList' a
upSList (Sing [])     = unsafeCoerce SNil'
upSList (Sing (a:as)) = unsafeCoerce $ SCons' (UnsafeSing a) (UnsafeSing as)

pattern SNil :: () => xs ~ '[] => Sing xs
pattern SNil <- (upSList -> SNil') where
  SNil = UnsafeSing []

pattern SCons :: () => aas ~ (a ': as) => Sing a -> Sing as -> Sing aas
pattern SCons a as <- (upSList -> SCons' a as) where
  SCons (Sing a) (Sing as) = UnsafeSing (a:as)

{-# complete SNil, SCons #-}

instance SingI '[] where
  sing = SNil

instance (SingI a, SingI as) => SingI (a ': as) where
  sing = SCons sing sing

--------------------------------------------------------------------------------
-- * Singleton Products
--------------------------------------------------------------------------------

type SPair' :: forall a b. (a,b) -> Type
type role SPair' nominal
data SPair' t where
  SPair' :: Sing a -> Sing b -> SPair' '(a, b)

upSPair :: Sing a -> SPair' a
upSPair (Sing (a,b)) = unsafeCoerce $ SPair' (UnsafeSing a) (UnsafeSing b)

pattern SPair :: Sing a -> Sing b -> Sing '(a, b)
pattern SPair a b <- Sing (UnsafeSing -> a, UnsafeSing -> b) where
  SPair a b = UnsafeSing (fromSing a, fromSing b)

{-# complete SPair #-}

instance (SingI a, SingI b) => SingI '(a, b) where
  sing = SPair sing sing

