{-# language CPP #-}
{-# language AllowAmbiguousTypes #-}
{-# language BangPatterns #-}
{-# language BlockArguments #-}
{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ImportQualifiedPost #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language PatternSynonyms #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language QuasiQuotes #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneKindSignatures #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}
{-# language Unsafe #-}
{-# language ViewPatterns #-}
{-# OPTIONS_HADDOCK not-home #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Internal where

import Control.Applicative
import Control.Concurrent
import Data.Constraint
import Data.Function
import Data.IORef
import Data.Int
import Data.Kind
import Data.List.NonEmpty qualified as NE
import Data.Proxy
import Data.STRef
import Data.Some
import Data.Traversable
import Data.Type.Equality
import Data.Void
import Data.Word
import Foreign.Ptr
import Foreign.StablePtr
import GHC.Exts
import GHC.TypeLits as TL
import GHC.TypeNats as TN
import Language.Haskell.TH qualified as TH
import Numeric.Natural
import Text.Read hiding (Symbol)
import Type.Reflection
import Unsafe.Coerce

--------------------------------------------------------------------------------
-- * Structural Equality
--------------------------------------------------------------------------------

-- | A type with structural equality
--
-- @
-- x '==' y ==> f x '==' f y
-- @
class Eq a => StrictEq a
instance StrictEq (MVar a)
instance StrictEq (IORef a)
instance StrictEq (STRef s a)
instance StrictEq (Proxy a)
instance StrictEq ThreadId
instance StrictEq a => StrictEq (Const a b)
instance StrictEq Bool
instance StrictEq ()
instance StrictEq Void
instance StrictEq (Dict p)
instance StrictEq (p :- q)
instance StrictEq Ordering
instance StrictEq a => StrictEq (Maybe a)
instance (StrictEq a, StrictEq b) => StrictEq (a, b)
instance (StrictEq a, StrictEq b, StrictEq c) => StrictEq (a, b, c)
instance (StrictEq a, StrictEq b, StrictEq c, StrictEq d) => StrictEq (a, b, c, d)
instance (StrictEq a, StrictEq b, StrictEq c, StrictEq d, StrictEq e) => StrictEq (a, b, c, d, e)
instance (StrictEq a, StrictEq b) => StrictEq (Either a b)
instance StrictEq a => StrictEq [a]
instance StrictEq a => StrictEq (NE.NonEmpty a)
instance StrictEq (Ptr a)
instance StrictEq (StablePtr a)

--------------------------------------------------------------------------------
-- * Singletons
--------------------------------------------------------------------------------

type Sing :: forall k. k -> Type
type role Sing nominal
newtype Sing (a :: k) = SING { fromSing :: k }

instance (Typeable k, Show k) => Show (Sing (a :: k)) where
  showsPrec d (Sing k) = showParen (d > 10) $
    showString "Sing @" . showsPrec 11 (typeRep @k) . showChar ' ' . showsPrec 11 k

pattern Sing :: k -> Sing (a :: k)
pattern Sing x <- (SING x)

{-# complete Sing #-}

instance Eq (Sing a) where
  _ == _ = True

instance Ord (Sing a) where
  compare _ _ = EQ

instance StrictEq (Sing a)

-- assumes equality is structural.
instance StrictEq k => TestEquality (Sing :: k -> Type) where
  testEquality i j
    | fromSing i == fromSing j = Just (unsafeCoerce Refl)
    | otherwise = Nothing

--------------------------------------------------------------------------------
-- * Reflection
--------------------------------------------------------------------------------

type SingI :: forall k. k -> Constraint
class SingI (a :: k) where
  sing :: Sing a

-- bootstrapping singleton singletons
instance SingI k => SingI @(Sing k) ('SING a) where
  sing = SING sing

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
reify k f = ify# f (SING k) proxy#

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
  sing = SING $ Type $ typeRep @a

type SType' :: Type -> Type
data SType' a where
  SType' :: TypeRep a -> SType' (a :: Type)

upSType :: Sing a -> SType' a
upSType (Sing (Type t)) = unsafeCoerce (SType' t)

pattern SType :: TypeRep a -> Sing (a :: Type)
pattern SType t <- (upSType -> SType' t) where
  SType t = SING $ Type t

--------------------------------------------------------------------------------
-- * Lowering Nats
--------------------------------------------------------------------------------

instance {-# OVERLAPPABLE #-} KnownNat a => SingI a where
  sing = SING $ Nat $ TN.natVal (Proxy @a)

instance Show Nat where
  showsPrec d = showsPrec d . fromNat

instance Eq Nat where
  (==) = (==) `on` fromNat

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
-- * Integral types
-----------------------------------------------------------------------------

pattern Z :: Integral a => a
pattern Z = 0

pattern S :: Integral a => a -> a
pattern S n <- ((\case 0 -> Nothing; n -> Just $ n-1) -> Just n)
  where S n = n+1

{-# complete Z, S :: Natural #-}
{-# complete Z, S :: Nat #-}
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

data family Z# k :: k
data family S# k :: k -> k

class (Integral a, (Z::a) ~ NiceZ) => Nice a where
  type NiceZ :: a
  type NiceS :: a -> a
  sinj :: forall (n::a). Proxy# n -> S n :~: NiceS n

type Z :: forall k. k
type family Z :: k where
  Z = 0
  Z = NiceZ

type S :: forall k. k -> k
type family S (n::k) :: k where
  S n = 1 + n
  S n = NiceS n

concat <$> for
  [ ''Natural -- when GHC makes 'Natural' = 'Nat' this will not be 'Nice'
  , ''Integer
  , ''Int, ''Int8, ''Int16, ''Int32, ''Int64, ''IntPtr
  , ''Word, ''Word8, ''Word16, ''Word32, ''Word64, ''WordPtr
  ] \(TH.conT -> n) ->
  [d|instance Nice $(n) where
       type NiceZ = Z# $(n)
       type NiceS = S# $(n)
       sinj _ = Refl |]

type SIntegral' :: forall a. a -> Type
data SIntegral' (n :: a) where
  SZ' :: SIntegral' Z
  SS' :: Sing n -> SIntegral' (S n)

upSIntegral :: forall a (n::a). Integral a => Sing n -> SIntegral' n
upSIntegral (SING 0) = unsafeCoerce SZ'
upSIntegral (SING n) = unsafeCoerce $ SS' (SING (n-1))

-- shared for both injective types and for Nat

pattern SZ :: forall a (n::a). Integral a => n ~ Z => Sing n
pattern SZ <- (upSIntegral -> SZ') where
  SZ = SING 0

pattern SS :: forall a (n::a). Integral a => forall (n'::a). n ~ S n' => Sing n' -> Sing n
pattern SS n <- (upSIntegral -> SS' n) where
  SS (Sing n) = SING (S n)

{-# complete SS, SZ #-}

instance forall a (n::a). (Nice a, NiceS ~ S# a, SingI n) => SingI (S# a n) where
  sing = case sinj (proxy# @n) of
    Refl -> SS (sing @a @n)

instance forall a. (Integral a, Z ~ Z# a) => SingI (Z# a) where
  sing = SZ

--------------------------------------------------------------------------------
-- * Lifting Dict and types that are otherwise singleton
--------------------------------------------------------------------------------

-- used to fill in 'It' when the singular term can't be lifted
data family It# :: k
type family It :: k

type Singular k = SingI (It :: k)

it :: forall k. Singular k => k
it = reflect @k @It

type instance It = It# :: Dict p
instance p => SingI (It# :: Dict p) where
  sing = SING Dict

type instance It = It# :: p :- q
instance (p => q) => SingI (It# :: (p :- q)) where
  sing = SING (Sub Dict)

type instance It = 'SING It

type instance It = '()

type instance It = 'Proxy
type instance It = 'Const It
type instance It = '(It,It)
type instance It = '(It,It,It)
type instance It = '(It,It,It,It)
type instance It = '(It,It,It,It,It)
type instance It = '(It,It,It,It,It,It)
type instance It = '(It,It,It,It,It,It,It)
type instance It = '(It,It,It,It,It,It,It,It)
type instance It = '(It,It,It,It,It,It,It,It,It)

--------------------------------------------------------------------------------
-- * Lifting (Ptr a)
--------------------------------------------------------------------------------

data family FromWordPtr# :: WordPtr -> k

type MkPtr :: forall a. WordPtr -> Ptr a
type MkPtr = FromWordPtr#

instance SingI n => SingI (MkPtr n) where
  sing = SMkPtr sing

pattern SMkPtr :: Sing n -> Sing (MkPtr n)
pattern SMkPtr n <- Sing (SING . ptrToWordPtr -> n) where
  SMkPtr (Sing n) = SING $ wordPtrToPtr n

{-# complete SMkPtr #-}

--------------------------------------------------------------------------------
-- * Lifting (StablePtr a)
--------------------------------------------------------------------------------

data family FromPtr# :: Ptr a -> k

type MkStablePtr :: forall a. Ptr () -> StablePtr a
type MkStablePtr = FromPtr#

instance SingI n => SingI (MkStablePtr n) where
  sing = SMkStablePtr sing

pattern SMkStablePtr :: Sing n -> Sing (MkStablePtr n)
pattern SMkStablePtr n <- Sing (SING . castStablePtrToPtr -> n) where
  SMkStablePtr (Sing n) = SING $ castPtrToStablePtr n

{-# complete SMkStablePtr #-}

--------------------------------------------------------------------------------
-- * Lifting Char
--------------------------------------------------------------------------------

data family FromSymbol :: Symbol -> k

type MkChar :: Symbol -> Char
type MkChar = FromSymbol

instance KnownSymbol s => SingI (MkChar s) where
  sing = case symbolVal $ Proxy @s of
    [c] -> SING c
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
  sing = SING $ Symbol $ symbolVal $ Proxy @s

--------------------------------------------------------------------------------
-- * Singleton Lists
--------------------------------------------------------------------------------

{-
type SList# :: forall a. [a] -> Type
type role SList# nominal
data SList# a where
  SNil# :: SList# '[]
  (:%) :: Sing a -> Sing as -> SList# (a ': as)

infixr 5 :%

upSList :: Sing a -> SList# a
upSList (Sing [])     = unsafeCoerce SNil#
upSList (Sing (a:as)) = unsafeCoerce $ SING a :% SING as

pattern SNil :: () => xs ~ '[] => Sing xs
pattern SNil <- (upSList -> SNil#) where
  SNil = SING []

pattern (:#) :: () => aas ~ (a ': as) => Sing a -> Sing as -> Sing aas
pattern a :# as <- (upSList -> a :% as) where
  Sing a :# Sing as = SING (a:as)

infixr 5 :#

{-# complete SNil, (:#) #-}

instance SingI '[] where
  sing = SNil

instance (SingI a, SingI as) => SingI (a ': as) where
  sing = sing :# sing

--------------------------------------------------------------------------------
-- * Singleton NonEmpty Lists
--------------------------------------------------------------------------------

type SNonEmpty# :: forall a. NE.NonEmpty a -> Type
type role SNonEmpty# nominal
data SNonEmpty# a where
  (:|%) :: Sing a -> Sing as -> SNonEmpty# (a 'NE.:| as)

infixr 5 :|%

upSNonEmpty :: Sing a -> SNonEmpty# a
upSNonEmpty (Sing (a NE.:| as)) = unsafeCoerce $ SING a :|% SING as

pattern (:|#) :: () => aas ~ (a 'NE.:| as) => Sing a -> Sing as -> Sing aas
pattern a :|# as <- (upSNonEmpty -> a :|% as) where
  Sing a :|# Sing as = SING (a NE.:| as)

infixr 5 :|#

{-# complete (:|#) #-}

instance (SingI a, SingI as) => SingI (a 'NE.:| as) where
  sing = sing :|# sing

-}

--------------------------------------------------------------------------------
-- * Singleton Products
--------------------------------------------------------------------------------

{-
type SPair# :: forall a b. (a,b) -> Type
type role SPair# nominal
data SPair# t where
  SPair# :: Sing a -> Sing b -> SPair# '(a, b)

upSPair :: Sing a -> SPair# a
upSPair (Sing (a,b)) = unsafeCoerce $ SPair# (SING a) (SING b)

pattern SPair :: () => r ~ '(a,b) => Sing a -> Sing b -> Sing r
pattern SPair a b <- (upSPair -> SPair# a b) where
  SPair (Sing a) (Sing b) = SING (a, b)

{-# complete SPair #-}

instance (SingI a, SingI b) => SingI '(a, b) where
  sing = SPair sing sing

-}
