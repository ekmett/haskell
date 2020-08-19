{-# Language ConstraintKinds #-}
{-# Language TypeFamilies #-}
{-# Language DataKinds #-}
{-# Language PolyKinds #-}
{-# Language DefaultSignatures #-}
{-# Language ImportQualifiedPost #-}
{-# Language MultiParamTypeClasses #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language UndecidableSuperClasses #-}
{-# Language RankNTypes #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language QuantifiedConstraints #-}
{-# Language TypeApplications #-}
module Data.Category.Class
  ( Category(..)
  , Cat
  , obco
  , Y(..)
  , type (-:-)(..)
  , Trivial
  ) where


import Data.Coerce
import Data.Constraint
import Data.Type.Equality as Eq
import Data.Type.Coercion as Co
import GHC.Types
import Prelude hiding ((.),id)
import Control.Category qualified as Control

class Trivial (a :: i)
instance Trivial a

type Cat i = i -> i -> Type

class (Category k, Op k ~ k) => Groupoid k where
  inv :: k a b -> k b a

class 
  ( Op (Op k) ~ k
  , Ob (Op k) ~ Ob k
  , Ob (Co k) ~ Ob k
  , Groupoid (Co k)
  , Co (Co k) ~ Co k
  , Category (Op k)
  ) => Category (k :: Cat i) where
  type Ob k :: i -> Constraint
  type Ob k = Trivial

  type Op k :: i -> i -> Type
  type Op k = Y k

  type Co k :: Cat i
  type Co k = Coercion

  -- sub-category of coercions
  co :: forall a b. Co k a b -> k a b
  default co :: 
    ( Co k ~ Coercion
    , forall a b. Coercible a b => Coercible (k a a) (k a b)
    ) => forall a b. Co k a b -> k a b
  co (Coercion :: Coercion a b) = case obco @k @a of
      Sub Dict -> coerce (id :: k a a) :: k a b

  id :: Ob k a => k a a
  default id :: (Control.Category k, Ob k ~ Trivial, Ob k a) => k a a
  id = Control.id

  (.) :: k b c -> k a b -> k a c
  default (.) :: (Control.Category k, Ob k ~ Trivial, Ob k a) => k b c -> k a b -> k a c
  (.) = (Control..)

  src :: k a b -> Dict (Ob k a)
  default src :: (Ob k ~ Trivial) => k a b -> Dict (Ob k a)
  src _ = Dict

  tgt :: k a b -> Dict (Ob k b)
  default tgt :: (Ob k ~ Trivial) => k a b -> Dict (Ob k b)
  tgt _ = Dict

  op :: k a b -> Op k b a
  default op :: (Op k ~ Y k) => k a b -> Op k b a
  op = Y

  unop :: Op k b a -> k a b
  default unop :: (Op k ~ Y k) => Op k b a -> k a b
  unop (Y f) = f

obco :: forall k a. Category k => Ob (Co k) a :- Ob k a
obco = Sub $ case src (co (id :: Co k a a) :: k a a) of Dict -> Dict

newtype Y k a b = Y (k b a)

instance (Category k, Op k ~ Y k) => Category (Y k) where
  type Op (Y k) = k
  type Ob (Y k) = Ob k
  type Co (Y k) = Co k
  co f = Y (co (inv f))
  id = Y id
  Y f . Y g = Y (g . f)
  src (Y f) = tgt f
  tgt (Y f) = src f
  op (Y f) = f
  unop = Y

-- bi-implication
data p -:- q = Subs (p :- q) (q :- p)

instance Category (-:-) where
  type Op (-:-) = (-:-)
  type Co (-:-) = (-:-)
  co = id
  id = Subs id id
  Subs f f' . Subs g g' = Subs (f . g) (g' . f')
  op = inv 
  unop = inv 

instance Groupoid (-:-) where
  inv (Subs f g) = Subs g f

instance Category (:-) where
  type Co (:-) = (-:-)
  co (Subs f _) = f

instance Category (->) where
  co = coerceWith

instance Category (:~:) where
  type Co (:~:) = (:~:)
  type Op (:~:) = (:~:)
  co = id
  op = Eq.sym
  unop = Eq.sym

instance Groupoid (:~:) where
  inv = Eq.sym

instance Category Coercion where
  type Co Coercion = Coercion
  type Op Coercion = Coercion
  co = id
  op = Co.sym
  unop = Co.sym

instance Groupoid Coercion where
  inv = Co.sym
