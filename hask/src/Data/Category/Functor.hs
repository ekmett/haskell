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
{-# Language LambdaCase #-}
{-# Language StandaloneKindSignatures #-}
{-# Language ExplicitForAll #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language TypeApplications #-}
{-# Language QuantifiedConstraints #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

module Data.Category.Functor
  ( Functor(..)
  , ob
  , unmap
  , contramap
--  , type (~>)
--  , Nat(..)
--  , Hom(..)
  ) where

import Data.Category.Class
import Data.Coerce
import Data.Constraint
--import Data.These
import Data.Type.Equality as Eq
import Data.Type.Coercion as Co
-- import GHC.Types hiding (Nat)
import Prelude hiding (Functor(..),map,id,(.))
import Prelude qualified as P hiding (map)

class
  ( Category p 
  , Category q
  , Dual (Dual f) ~ Dual f
  , Functor (Op p) (Op q) (Dual f)
  -- , Functor (Co p) (Co q) f
  ) => Functor (p :: Cat i) (q :: Cat j) (f :: i -> j) | f p -> q where
  type Dual f :: i -> j

  comap :: Co p a b -> Co q (f a) (f b)

  map :: p a b -> q (f a) (f b)
  default map :: (f ~~ g, P.Functor g, p ~~ (->), q ~~ (->)) => p a b -> q (f a) (f b)
  map = P.fmap

  dual :: Co q (f a) (Dual f a)
  default dual :: 
    ( Co q ~ Coercion
    , g ~ Dual f
    , forall x. Coercible (f x) (g x)
    ) => Co q (f a) (Dual f a)
  dual = Coercion

unmap :: Functor p q f => Op p b a -> Op q (f b) (f a)
unmap f = op (map (unop f))

ob :: forall f p q a. Functor p q f => Ob p a :- Ob q (f a)
ob = Sub $ case src (map (id :: p a a) :: q (f a) (f a)) of Dict -> Dict

contramap :: Functor p q f => Op p b a -> q (f a) (f b)
contramap = map . unop

{-
class (Category k, Ob k a, OB (Op k) a) => OB (k :: Cat i) (a :: i)
instance (Category k, Ob k a, OB (Op k) a) => OB (k :: Cat i) (a :: i)

instance Category k => Functor k (-:-) (OB k) where
  type Dual (OB k) = OB (Op k)
  comap = undefined
  map f = Sub $ case tgt f of
    Dict -> Dict
  dual = Subs (Sub Dict) (Sub Dict)
-}
{-

type family DefaultCat (i :: Type) = (res :: Cat i) | res -> i
type instance DefaultCat Type = (->)
type instance DefaultCat Constraint = (:-)
-- type instance DefaultCat (i -> j) = Nat (DefaultCat i) (DefaultCat j)

-- instance Functor p (:-) Trivial where
--  map _ = Sub Dict



  dual 


{-
type family DefaultDual (f :: i -> j) :: i -> j
type instance DefaultDual f = Un f
type instance DefaultDual f = UnC f

data family Un (f :: i -> k) (a :: i) :: k
newtype instance Un (f :: i -> Type) (a :: i) = Un { runUn :: f a }
newtype instance Un (f :: i -> j -> Type) (a :: i) (b :: j) = Un2 { runUn2 :: f a b }

class OpTrivial (k :: Cat i) (a :: i)
instance OpTrivial k a

instance (Functor (Op p) (Op q) f, Dual f ~ Un f) => Functor p q (Un f) where
  type Dual (Un f) = f
  type Dom (Un f) = Op (Dom f)
  type Cod (Un f) = Op (Cod f)
  map f = undefined -- op (map f)

instance (Functor f, Dual f ~ Un2 f) => Functor (Un2 f) where
  type Dual (Un2 f) = f
  type Dom (Un2 f) = Op (Dom f)
  type Cod (Un2 f) = Op (Cod f)
  map f = undefined -- op (map (unop f))
-}

{-


-- type (~>) :: (forall i. i -> i -> Type)
-- type (~>) = (forall i. DefaultCat i)
-- type family (~>) :: i -> i -> Type where (~>) = DefaultCat i 

data Nat (p :: Cat i) (q :: Cat j) (f :: i -> j) (g :: i -> j)
  = (Functor p q f, Functor p q g) => Nat { runNat :: forall a. Ob p a => q (f a) (g a) }

instance (Category p, Category q) => Category (Nat p q) where
  type Ob (Nat p q) = Functor p q
  id = Nat id1 where
    id1 :: forall f x. (Functor p q f, Ob p x) => q (f x) (f x)
    id1 = id \\ (ob @f @p @q @x)
  Nat f . Nat g = Nat (f . g)
  src Nat{} = Dict
  tgt Nat{} = Dict

instance (Category p, Category q) => Functor (Nat p q) (Y (Nat (Nat p q) (->))) (Nat p q) where map = unmap
instance (Category p, Category q) => Functor (Y (Nat p q)) (Nat (Nat p q) (->)) (Nat p q) where
  map f = Nat (. unop f)
instance (Category p, Category q) => Functor (Y (Nat p q)) (Y (->)) (Nat p q f) where map = unmap
instance (Category p, Category q) => Functor (Nat p q) (->) (Nat p q f) where
  map = (.)

newtype Hom (k :: Cat i) (a :: i) (b :: i) = Hom { runHom :: k a b }
type role Hom representational nominal nominal

-- deriving instance Category k => Category (Hom k)
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

-- big messy instance
-- instance (Op p ~ Y p, Functor p (Op q) f) => Functor (Y p) q f where map = unmap

{-
instance (Category k, Op k ~ Y k) => Functor (Y k) (Y (->)) (Hom k e) where map = unmap
instance Category k => Functor k (->) (Hom k e) where
  map = go where
    go :: forall a b c. k b c -> Hom k a b -> Hom k a c
    go = coerce ((.) :: k b c -> k a b -> k a c)

instance Category k => Functor k (Y (Nat k (->))) (Hom k) where map = unmap
instance Category k => Functor (Y k) (Nat k (->)) (Hom k) where
  map f = Nat \(Hom g) -> Hom (g . unop f)
-}

instance Functor (:~:) (:~:) (:~:) where map = Eq.apply id
instance Functor (:~:) (:~:) ((:~:) a) where map = Eq.apply id

instance Functor (:~:) (:~:) Coercion where map Eq.Refl = id
instance Functor (:~:) (:~:) (Coercion a) where map Eq.Refl = id
-- instance Functor Coercion Coercion (Coercion e) where
--  map (co :: Coercion a b) = gcoerceWith co (id :: Coercion a a)

instance Functor (Y (->)) (Y (->)) ((->) e) where map = unmap
instance Functor (->) (->) ((->) e)

instance Functor (->) (Y (Nat (->) (->))) (->) where map = unmap
instance Functor (Y (->)) (Nat (->) (->)) (->) where map f = Nat (. unop f)

instance (Category p, Op p ~ Y p) => Functor (Y p) (->) (Y p a) where map = (.)
instance (Category p, Op p ~ Y p) => Functor p (Y (->)) (Y p a) where map = unmap

instance (Category p, Op p ~ Y p) => Functor (Y p) (Y (Nat (Y p) (->))) (Y p) where map = unmap
instance (Category p, Op p ~ Y p) => Functor p (Nat (Y p) (->)) (Y p) where map f = Nat (. Y f)

instance Functor (Y (:-)) (Y (->)) Dict where map = unmap
instance Functor (:-) (->) Dict where map p Dict = case p of Sub q -> q

instance Functor (Y (:-)) (Y (->)) ((:-) e) where map = unmap
instance Functor (:-) (->) ((:-) e) where map = (.)

instance Functor (Y (:-)) (Nat (:-) (->)) (:-) where map f = Nat (. unop f)
instance Functor (:-) (Y (Nat (:-) (->))) (:-) where map = unmap

{-
instance Functor ((,) e)
instance Functor (Either e)
instance Functor []
instance Functor .Maybe
instance Functor IO
instance Functor (,) where
  map f = Nat \(a,b) -> (f a, b)

instance Functor These where
  map f = Nat \case
    This a -> This (f a)
    These a b -> These (f a) b
    That b -> That b

instance Functor (These a)

instance Functor Either where
  map f0 = Nat (go f0) where
    go :: (a -> b) -> Either a c -> Either b c
    go f (Left a)  = Left (f a)
    go _ (Right b) = Right b
-}
-}
-}
