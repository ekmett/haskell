{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language GADTs #-}
{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}
{-# Language PatternSynonyms #-}
{-# Language EmptyCase #-}
{-# Language RankNTypes #-}
module Nat where

import Control.Category
import Control.Monad (join)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import GHC.Types (Type)
import Prelude hiding ((.),id,pred)
import qualified Prelude

-- judgments as types

-- naive naturals with addition bolted in
-- these could be useful for decorating vectors stored as trees
-- with 'natural' indices/offsets

data Nat
  = Z
  | S !Nat
  | Add !Nat !Nat
  deriving Show

-- brute force equivalences
data Same :: Nat -> Nat -> Type where
  Symm    :: Same a b -> Same b a
  Succ    :: Same m n -> Same ('S m) ('S n)
  Assoc   :: Same ('Add ('Add a b) c) ('Add a ('Add b c))
  Z_Add   :: Same a ('Add 'Z a)
  S_Add   :: Same ('S ('Add m n)) ('Add ('S m) n)
  Add_Z   :: Same a ('Add a 'Z)
  -- Add_S   :: Same ('S ('Add m n)) ('Add m ('S n))
  Id      :: Same n n
  Sum     :: Same a b -> Same c d -> Same ('Add a c) ('Add b d)
  Comp    :: Same b c -> Same a b -> Same a c

instance Show (Same m n) where
  showsPrec d (Symm f) = showParen (d > 10) $ showString "Symm " . showsPrec 11 f
  showsPrec d (Succ f) = showParen (d > 10) $ showString "Succ " . showsPrec 11 f
  showsPrec _ Assoc = showString "Assoc"
  showsPrec _ Z_Add = showString "Z_Add"
  showsPrec _ S_Add = showString "Z_Add"
  showsPrec _ Add_Z = showString "Add_Z"
  -- showsPrec _ Add_S = showString "Add_S"
  showsPrec _ Id = showString "Id"
  showsPrec d (Sum l r) = showParen (d > 10) $ showString "Sum " . showsPrec 11 l . showChar ' ' . showsPrec 11 r
  showsPrec d (Comp l r) = showParen (d > 10) $ showString "Comp " . showsPrec 11 l . showChar ' ' . showsPrec 11 r

instance Category Same where
  id = Id
  Id . f = f
  f . Id = f
  -- toy local simplifications
  Symm f . Symm g = Symm (g . f)
  Assoc . Symm Assoc = Id
  Symm Assoc . Assoc = Id
  -- common case
  f . g = Comp f g

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)
  SAdd :: SNat n -> SNat m -> SNat ('Add n m)

instance Show (SNat n) where
  showsPrec _ SZ = showString "SZ"
  showsPrec d (SS n) = showParen (d > 10) $ showString "SS " . showsPrec 11 n
  showsPrec d (SAdd n m) = showParen (d > 10) $ showString "SAdd " . showsPrec 11 n . showChar ' ' . showsPrec 11 m

class KnownNat n where
  snat :: SNat n

instance KnownNat Z where
  snat = SZ

instance KnownNat n => KnownNat (S n) where
  snat = SS snat

instance (KnownNat n, KnownNat m) => KnownNat (Add n m) where
  snat = SAdd snat snat

withSNat :: SNat n -> (KnownNat n => r) -> r
withSNat SZ f = f
withSNat (SS n) f = withSNat n f
withSNat (SAdd m n) f = withSNat m (withSNat n f)

type family HeadNormal (n :: Nat) :: Nat where
  HeadNormal 'Z = 'Z
  HeadNormal ('S n) = 'S n
  HeadNormal ('Add m n) = HeadNormalPlus m n

type family HeadNormalPlus (n :: Nat) (m :: Nat) :: Nat where
  HeadNormalPlus 'Z m = HeadNormal m
  HeadNormalPlus ('S n) m = 'S ('Add n m)
  HeadNormalPlus ('Add n m) o = HeadNormalPlus n ('Add m o)

type family Pred (n :: Nat) :: Nat where
  Pred ('S n) = n
  Pred ('Add m n) = PredPlus m n

type family PredPlus (m :: Nat) (n :: Nat) :: Nat where
  PredPlus 'Z m = Pred m
  PredPlus ('S n) m = 'Add n m
  PredPlus ('Add m n) o = PredPlus m ('Add n o)

headNormal :: SNat n -> Same n (HeadNormal n)
headNormal SZ = Id
headNormal (SS _) = Id
headNormal (SAdd m n) = headNormalPlus m n

headNormalPlus :: SNat n -> SNat m -> Same ('Add n m) (HeadNormalPlus n m)
headNormalPlus SZ m = headNormal m . Symm Z_Add
headNormalPlus (SS _) _ = Symm S_Add
headNormalPlus (SAdd n m) o = headNormalPlus n (SAdd m o) . Assoc

pred :: SNat n -> Maybe (SNat (Pred n))
pred SZ = Nothing
pred (SS n) = Just n
pred (SAdd m n) = predPlus m n

predPlus :: SNat n -> SNat m -> Maybe (SNat (PredPlus n m))
predPlus SZ m = pred m
predPlus (SS n) m = Just (SAdd n m)
predPlus (SAdd n m) o = predPlus n (SAdd m o)

-- use to match on these so we can pretend the Add stuff isn't here
pattern VZ :: () => (HeadNormal n ~ 'Z) => SNat n
pattern VZ <- (join (same . headNormal) -> SZ) -- where VZ = join (unsame . unheadNormal) SZ

pattern VS :: () => (HeadNormal n ~ 'S n') => SNat n' -> SNat n
pattern VS n' <- (join (same . headNormal) -> SS n')

{-# complete VS, VZ #-}

type family CanonicalPlus (n :: Nat) (m :: Nat) :: Nat where
  CanonicalPlus 'Z n = Canonical n
  CanonicalPlus ('S n) m = 'S (CanonicalPlus n m)
  CanonicalPlus ('Add m n) o = CanonicalPlus m ('Add n o)

type family Canonical (n :: Nat) :: Nat where
  Canonical 'Z = 'Z
  Canonical ('S n) = 'S (Canonical n)
  Canonical ('Add m n) = CanonicalPlus m n

canonical :: SNat n -> Same n (Canonical n)
canonical SZ = Id
canonical (SS n) = Succ (canonical n)
canonical (SAdd n m) = canonicalPlus n m

canonicalPlus :: SNat n -> SNat m -> Same ('Add n m) (CanonicalPlus n m)
canonicalPlus SZ n = canonical n . Symm Z_Add
canonicalPlus (SS n) m = Succ (canonicalPlus n m) . Symm S_Add
canonicalPlus (SAdd m n) o = canonicalPlus m (SAdd n o) . Assoc

equate :: SNat n -> SNat m -> Maybe (Same n m)
equate (SAdd SZ m) n = (. Symm Z_Add) <$> equate m n
equate m (SAdd SZ n) = (Z_Add .) <$> equate m n
equate (SAdd (SS m) n) o = (. Symm S_Add) <$> equate (SS (SAdd m n)) o
equate m (SAdd (SS n) o) = (S_Add .) <$> equate m (SS (SAdd n o))
equate (SAdd (SAdd m n) o) p = (. Assoc) <$> equate (SAdd m (SAdd n o)) p
equate m (SAdd (SAdd n o) p) = (Symm Assoc .) <$> equate m (SAdd n (SAdd o p))
equate SZ SZ         = Just Id
equate (SS n) (SS m) = Succ <$> equate n m
equate SZ (SS _) = Nothing
equate (SS _) SZ = Nothing

class ActSame f where
  same :: Same n m -> f n -> f m
  unsame :: Same m n -> f n -> f m
  unsame = same . Symm

instance ActSame SNat where
  same Id n = n
  same (Comp f g) n = same f (same g n)
  same (Succ f) (SS n) = SS (same f n)
  same (Symm k) n = unsame k n
  same Assoc (SAdd (SAdd a b) c) = SAdd a (SAdd b c)
  same Z_Add n = SAdd SZ n
  same S_Add (SS (SAdd n m)) = SAdd (SS n) m
  same Add_Z n = SAdd n SZ
  -- same Add_S (SS (SAdd n m)) = SAdd n (SS m)
  same (Sum l r) (SAdd m n) = SAdd (same l m) (same r n)
  unsame Id n = n
  unsame (Comp f g) n = unsame g (unsame f n)
  unsame (Succ f) (SS n) = SS (unsame f n)
  unsame (Symm k) n = same k n
  unsame Assoc (SAdd a (SAdd b c)) = (SAdd (SAdd a b) c)
  unsame Z_Add (SAdd SZ n) = n
  unsame S_Add (SAdd (SS n) m) = SS (SAdd n m)
  unsame Add_Z (SAdd n SZ) = n
  -- unsame Add_S (SAdd n (SS m)) = SS (SAdd n m)
  unsame (Sum l r) (SAdd m n) = SAdd (unsame l m) (unsame r n)

symm :: Same m n -> Same n m
symm (Symm f) = f
symm Id = Id
symm f = Symm f

class Valued t where
  value :: t -> Int

instance Valued Nat where
  value Z = 0
  value (S n) = 1 + value n
  value (Add l r) = value l + value r

instance Valued (SNat n) where
  value SZ = 0
  value (SS n) = 1 + value n
  value (SAdd l r) = value l + value r

-- finite numbers with additions bolted in

data Fin (n :: Nat) where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)
  FL :: Fin n -> Fin ('Add n m)
  FR :: SNat n -> Fin m -> Fin ('Add n m)

instance Valued (Fin n) where
  value FZ = 0
  value (FS n) = 1 + value n
  value (FL l) = value l
  value (FR l r) = value l + value r

-- finite numbers with additions bolted in

instance Show (Fin n) where
  showsPrec _ FZ = showString "FZ"
  showsPrec d (FS n) = showParen (d > 10) $ showString "FS " . showsPrec 11 n
  showsPrec d (FL n) = showParen (d > 10) $ showString "FL " . showsPrec 11 n
  showsPrec d (FR n m) = showParen (d > 10) $ showString "FR " . showsPrec 11 n . showChar ' ' . showsPrec 11 m

instance ActSame Fin where
  same Id n = n
  same (Comp f g) n = same f (same g n)
  same (Symm k) n = unsame k n
  same (Succ _) FZ = FZ
  same (Succ f) (FS n) = FS (same f n)
  same Assoc (FL (FL a)) = FL a
  same Assoc (FL (FR a b)) = FR a (FL b)
  same Assoc (FR (SAdd a b) c) = FR a (FR b c)
  same Z_Add n = FR SZ n
  same S_Add FZ = FL FZ
  same S_Add (FS (FL n)) = FL (FS n)
  same S_Add (FS (FR n m)) = FR (SS n) m
  same Add_Z n = FL n
  same (Sum l _) (FL n) = FL (same l n)
  same (Sum l r) (FR n k) = FR (same l n) (same r k)
  unsame Id n = n
  unsame (Succ _) FZ = FZ
  unsame (Succ f) (FS n) = FS (unsame f n)
  unsame (Comp f g) n = unsame g (unsame f n)
  unsame (Symm k) n = same k n
  unsame Assoc (FL a) = FL (FL a)
  unsame Assoc (FR a (FL b)) = FL (FR a b)
  unsame Assoc (FR a (FR b c)) = FR (SAdd a b) c
  unsame Z_Add (FR SZ n) = n
  unsame Z_Add (FL x) = case x of
  unsame S_Add (FL FZ) = FZ
  unsame S_Add (FL (FS n)) = FS (FL n)
  unsame S_Add (FR (SS n) m) = FS (FR n m)
  unsame Add_Z (FL n) = n
  unsame Add_Z (FR _ m) = case m of
  unsame (Sum l _) (FL n) = FL (unsame l n)
  unsame (Sum l r) (FR n k) = FR (unsame l n) (unsame r k)

-- playing around at the value level with naturals equipped with Add

predNat :: Nat -> Maybe Nat
predNat Z = Nothing
predNat (S n) = Just n
predNat (Add n m) = case predNat n of
  Just n' -> Just (Add n' m)
  Nothing -> predNat m

instance Eq Nat where
  (==) = (==) `on` toInteger

instance Ord Nat where
  compare = compare `on` toInteger

-- dumb naturals
instance Num Nat where
  Z + n = n
  n + Z = n
  n + m = Add n m
  Z * n = Z
  S n * m = n + (n * m)
  n - m = fromInteger (toInteger n - toInteger m)
  negate n = case predNat n of
    Nothing -> Z
    _ -> error "negative natural"
  abs = id
  signum Z = Z
  signum (Add l r) = case signum l of
    Z -> signum r
    n -> n
  fromInteger 0 = Z
  fromInteger n
    | n > 0 = S (fromInteger (n - 1))
    | otherwise = error "negative natural"

instance Integral Nat where
  toInteger Z = 0
  toInteger (S n) = 1 + toInteger n
  toInteger (Add n m) = toInteger n + toInteger m
  quotRem a b = case quotRem (toInteger a) (toInteger b) of
    (q,r) -> (fromInteger q, fromInteger r)

instance Real Nat where
  toRational = toRational . toInteger

instance Enum Nat where
  succ = S
  pred = fromMaybe (error "pred 0") . predNat
  toEnum = fromIntegral
  fromEnum = value

