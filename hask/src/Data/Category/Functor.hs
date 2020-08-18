{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language FunctionalDependencies #-}
{-# Language UndecidableInstances #-}
{-# Language UndecidableSuperClasses #-}
{-# Language RankNTypes #-}
{-# Language KindSignatures #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language GADTs #-}
{-# Language ScopedTypeVariables #-}
{-# Language DefaultSignatures #-}
{-# Language ImportQualifiedPost #-}
{-# Language TypeFamilyDependencies #-}
{-# Language StandaloneDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DerivingVia #-}
{-# Language BlockArguments #-}
{-# Language RoleAnnotations #-}
module Data.Category.Functor
  ( Functor(..)
  , ob
  , FunctorOf
  , contramap
  , DomHack
  , DefaultCat
  , Nat(..)
  , Hom(..)
  ) where

import Data.Category.Class
import Data.Constraint
import GHC.Types hiding (Nat)
import Prelude hiding (Functor(..),map,id,(.))
import Prelude qualified

type family DomHack (f :: i -> j) (k :: Cat i) :: Cat i where
  DomHack p p = Op p
  DomHack f p = p

type family DefaultCat (i :: Type) = (res :: Cat i) | res -> i
type instance DefaultCat Type = (->)
type instance DefaultCat Constraint = (:-)
type instance DefaultCat (i -> j) = Nat (DefaultCat i) (DefaultCat j)

class
  ( Category (Dom f)
  , Category (Cod f)
  ) => Functor (f :: i -> j) where

  type Dom f :: Cat i
  type Dom (f :: i -> j) = DomHack f (DefaultCat i)

  type Cod f :: Cat j
  type Cod (f :: i -> j) = DefaultCat j

  map :: Dom f a b -> Cod f (f a) (f b)
  default map :: (f ~~ g, Prelude.Functor g, Dom f ~~ (->), Cod f ~~ (->)) => Dom f a b -> Cod f (f a) (f b)
  map = Prelude.fmap

ob :: forall f a. Functor f => Ob (Dom f) a :- Ob (Cod f) (f a)
ob = Sub $ case src (map id :: Cod f (f a) (f a)) of Dict -> Dict

contramap :: Functor f => Op (Dom f) b a -> Cod f (f a) (f b)
contramap = map . unop

class    (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f | f -> p q
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

data Nat (p :: Cat i) (q :: Cat j) (f :: i -> j) (g :: i -> j)
  = (FunctorOf p q f, FunctorOf p q g) => Nat { runNat :: forall a. Ob p a => q (f a) (g a) }

newtype Hom (k :: Cat i) (a :: i) (b :: i) = Hom { runHom :: k a b }
type role Hom representational nominal nominal


{-
instance Category k => Category (Hom k) where
  type Ob (Hom k) = Ob k
  type Op (Hom k) = Hom (Op k)
  id = Hom id
  Hom f . Hom g = Hom (f . g)
  src (Hom f) = src f
  tgt (Hom f) = tgt f
  op (Hom f) = Hom (op f)
  unop (Hom f) = Hom (unop f)
-}

instance Category k => Functor (Hom k e :: i -> Type) where
  type Dom (Hom k e) = k
  type Cod (Hom k e) = (->)
  map f (Hom g) = Hom (f . g)

instance Category k => Functor (Hom k :: i -> i -> Type) where
  type Dom (Hom k) = Op k
  type Cod (Hom k) = Nat k (->)
  map f = Nat \(Hom g) -> Hom (g . unop f)

instance (Category p, Category q) => Category (Nat p q) where
  type Ob (Nat p q) = FunctorOf p q
  id = Nat id1 where
    id1 :: forall f x. (FunctorOf p q f, Ob p x) => q (f x) (f x)
    id1 = id \\ (ob :: Ob p x :- Ob q (f x))
  Nat f . Nat g = Nat (f . g)
  src Nat{} = Dict
  tgt Nat{} = Dict

instance (Category p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Y (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  map (Y f) = Nat (. f)

instance (Category p, Category q) => Functor (Nat p q f) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  map = (.)

instance Functor ((->) e)

-- deriving via (Hom (->)) instance Functor (->)
instance Functor (->) where map f = Nat (. unop f)

instance (Category p, Op p ~ Y p) => Functor (Y p a) where
  type Dom (Y p a) = Y p
  type Cod (Y p a) = (->)
  map = (.)

instance (Category p, Op p ~ Y p) => Functor (Y p) where
  type Dom (Y p) = p
  type Cod (Y p) = Nat (Y p) (->)
  map f = Nat (. Y f)

instance Functor Dict where
  map p Dict = case p of
    Sub q -> q

instance Functor ((:-) e) where
  map = (.)

instance Functor (:-) where
  map (Y f) = Nat (. f)

instance Functor ((,) e)
instance Functor (Either e)
instance Functor []
instance Functor Prelude.Maybe
instance Functor IO
instance Functor (,) where
  map f = Nat \(a,b) -> (f a, b)

instance Functor Either where
  map f0 = Nat (go f0) where
    go :: (a -> b) -> Either a c -> Either b c
    go f (Left a)  = Left (f a)
    go _ (Right b) = Right b
