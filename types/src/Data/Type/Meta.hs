{-# language AllowAmbiguousTypes #-}
{-# language BangPatterns #-}
{-# language BlockArguments #-}
{-# language PatternSynonyms #-}
{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language ImportQualifiedPost #-}
{-# language IncoherentInstances #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneKindSignatures #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Meta
  ( type (!->)(..)
  , MkMeta
  , type (!=>)
  , SFunctor(..)
  , SBifunctor(..)
  , (!!)
  , trans
  , refl
  , mapSing
  , unmapSing
  , toMe
  , fromMe
  , No(..)
  , fromNo
  , apply
  -- Products
  , weaken1
  , weaken2
  -- Types
  , stypeRep
  , weakenT1
  , weakenT2
  , arg
  -- Constraints
  , (!\),(\!),(\\)
  , homo
  , nohomo
  , type (&)
  , mapSingC
  , unmapSingC
  , fromC
  , weakenC1
  , weakenC2
  ) where

import Control.Applicative
import Control.Category
import Data.Constraint ((:-)(..), Dict(..))
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Kind
import Data.List.NonEmpty qualified as NE
import Data.Type.Internal
import Data.Type.Internal.Instances
import Data.Void
import Prelude hiding (id,(.),(!!))
import Type.Reflection

type (!->) :: forall i j. i -> j -> Type
type role (!->) nominal nominal
newtype a !-> b = Subs (Sing a => Sing b)
infixr 0 !->

type MkMeta = Me# :: p !-> q
type instance Me = MkMeta :: p !-> q
instance (Sing p => SingI q, r ~ MkMeta) => SingI @(p !-> q) r where
  sing = SING (Subs sing)




withDict :: forall q r. Sing @Constraint q => (q => r) -> r
withDict r = case sing @_ @q of
  SConstraint -> r

apply :: '(a !=> b, a) !-> b
apply = unmapSing \case
 STuple2 SConstraint p -> withSing p sing

class (Sing p => SingI q) => p !=> q
instance (Sing p => SingI q) => p !=> q

-- pattern SSubs :: (p !=> q) -> Sing (MkMeta :: p !-> q)
-- wat :: Sing (p !=> q) -> Sing (Me# :: p !-> q)

{-
apply :: forall i j (a::i) (b::j). '(a !-> b, a) !-> b
apply = unmapSing \case
 STuple2 (Sing x) p -> _ x p
-}

-- withSingI p (the x)

{-
curry :: ('(a,b) !-> c) -> a !-> b !=> c
curry f = unmapSing \a -> unmapSing \b -> mapSing f (STuple (a b))
-}

toMe :: Singular k => a !-> Me @k
toMe = unmapSing \_ -> me

fromMe :: forall i j (a::j). Singular i => (Me @i !-> a) -> j
fromMe f = the $ mapSing f $ sing @i @Me

class No k where
  no :: k -> b

instance No Void where
  no = absurd

-- ex-falso, which is probably dangerous in a lazy non-total language
fromNo :: forall k (a::k) b. No k => a !-> b
fromNo = Subs $ no $ reflect @_ @a

(!!) :: Sing p => (Sing q => r) -> (p !-> q) -> r
r !! Subs sq = withSing sq r

(\!) :: p => (Sing q => r) -> (p !-> q) -> r
r \! Subs sq = withSing sq r

(!\) :: forall p q r. Sing p => (q => r) -> (p !-> q) -> r
r !\ Subs sq = withSing sq $ withDict @q r

(\\) :: forall p q r. p => (q => r) -> (p !-> q) -> r
r \\ Subs sq = withSing sq $ withDict @q r

instance Category (!->) where
  id = Subs sing
  f . g = Subs $ sing !! f !! g

-- note this is polykinded
trans :: (b !-> c) -> (a !-> b) -> a !-> c
trans f g = Subs $ sing !! f !! g

refl :: a !-> a
refl = Subs sing

homo :: (a !-> b) -> a :- b
homo f = Sub $ case f of
  Subs SConstraint -> Dict

nohomo :: forall a b. (a :- b) -> a !-> b
nohomo f = Subs $ case sing @_ @a of
  SConstraint -> case f of
    Sub Dict -> SConstraint

mapSing :: (a !-> b) -> Sing a -> Sing b
mapSing f s = withSing s $ sing !! f

unmapSing :: (Sing a -> Sing b) -> a !-> b
unmapSing f = Subs (f sing)

mapSingC :: (a :- b) -> Sing a -> Sing b
mapSingC = mapSing . nohomo

unmapSingC :: (Sing a -> Sing b) -> a :- b
unmapSingC = homo . unmapSing

fromC :: forall a b. (a => Sing b) -> a !-> b
fromC b = Subs $ case sing @_ @a of
  SConstraint -> b

weaken1 :: '(a,b) !-> a
weaken1 = unmapSing \case
  STuple2 a _ -> a

weaken2 :: '(a,b) !-> b
weaken2 = unmapSing \case
  STuple2 _ b -> b

class (a, b) => a & b
instance (a, b) => a & b

weakenC1 :: a&b !-> a
weakenC1 = fromC SConstraint

weakenC2 :: a&b !-> b
weakenC2 = fromC SConstraint

-- for f = (,) -- this = fst
weakenT1 :: forall (a::Type) (b::Type) (f :: Type -> Type -> Type). f a b !-> a
weakenT1 = unmapSing \case
  SType (App (App _ a) _) -> SType a

-- for f = (,) -- this = snd
weakenT2 :: forall (a::Type) (b::Type) (f :: Type -> Type -> Type). f a b !-> b
weakenT2 = arg

arg :: forall (f::Type -> Type) (b::Type). f b !-> b
arg = unmapSing \case
  SType (App _ b) -> SType b

stypeRep :: forall (a :: Type). Typeable a !-> a
stypeRep = fromC $ SType $ typeRep @a

-- template haskell should be able to readily derive SFunctor
-- and SBifunctor for each pattern it builds of sufficient arity

type SFunctor :: (i -> j) -> Constraint
class SFunctor f where
  smap :: (a !-> b) -> f a !-> f b

instance SFunctor (Typeable @Type) where
  smap (f :: a !-> b) = fromC $ case mapSing f (SType $ typeRep @a) of
    SType x -> withTypeable x SConstraint

instance SFunctor 'Left where
  smap (f :: a !-> b) = unmapSing \case
    SLeft x -> SLeft (mapSing f x)

instance SFunctor 'Right where
  smap (f :: a !-> b) = unmapSing \case
    SRight x -> SRight (mapSing f x)

instance SFunctor 'Const where
  smap (f :: a !-> b) = unmapSing \case
    SConst x -> SConst (mapSing f x)

instance SFunctor 'Just where
  smap (f :: a !-> b) = unmapSing \case
    SJust x -> SJust (mapSing f x)

instance SFunctor ('(,) x) where
  smap = sbimap id

instance SFunctor ((&) x) where
  smap = sbimap id

instance SFunctor (f :: Type -> Type) where
  smap f = unmapSing \case
    SType (App x a) -> SType $ App x $ case mapSing f (SType a) of
       SType y -> y

instance SFunctor 'Compose where
  smap f = unmapSing \case
    SCompose a -> SCompose (mapSing f a)

instance SFunctor 'Identity where
  smap f = unmapSing \case
    SIdentity a -> SIdentity (mapSing f a)

instance SFunctor ('(:) a) where
  smap = sbimap id

instance SFunctor ('(NE.:|) a) where
  smap = sbimap id

type SBifunctor :: (i -> j -> k) -> Constraint
class SBifunctor t where
  sbimap :: (a !-> b) -> (c !-> d) -> t a c !-> t b d

instance SBifunctor '(,) where
  sbimap f g = unmapSing \case
    STuple2 a b -> STuple2 (mapSing f a) (mapSing g b)

instance SBifunctor '(:) where
  sbimap f g = unmapSing \case
    a :# b -> mapSing f a :# mapSing g b

instance SBifunctor '(NE.:|) where
  sbimap f g = unmapSing \case
    a :|# b -> mapSing f a :|# mapSing g b

instance SBifunctor (&) where
  sbimap f g = nohomo $ Sub $ Dict \\ f \\ g

instance SBifunctor (f :: Type -> Type -> Type) where
  sbimap f g = unmapSing \case
    SType (App (App t a) c) -> SType $ App
      (App t case mapSing f (SType a) of SType b -> b)
             case mapSing g (SType c) of SType d -> d

