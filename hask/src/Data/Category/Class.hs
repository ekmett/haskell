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
module Data.Category.Class
  ( Category(..)
  , Cat
  , Y(..)
  ) where

import Data.Constraint
import Data.Type.Equality as Eq
import Data.Type.Coercion as Co
import GHC.Types
import Prelude hiding ((.),id)
import Control.Category qualified as Control

class Trivial (k :: i -> i -> Type) (a :: i)
instance Trivial k a

type Cat i = i -> i -> Type

class 
  ( Op (Op k) ~ k
  , Ob (Op k) ~ Ob k
  , Category (Op k)
  ) => Category (k :: Cat i) where
  type Ob k :: i -> Constraint
  type Ob k = Trivial k

  type Op k :: i -> i -> Type
  type Op k = Y k

  id :: Ob k a => k a a
  default id :: (Control.Category k, Ob k ~ Trivial k, Ob k a) => k a a
  id = Control.id

  (.) :: k b c -> k a b -> k a c
  default (.) :: (Control.Category k, Ob k ~ Trivial k, Ob k a) => k b c -> k a b -> k a c
  (.) = (Control..)

  src :: k a b -> Dict (Ob k a)
  default src :: (Ob k ~ Trivial k) => k a b -> Dict (Ob k a)
  src _ = Dict

  tgt :: k a b -> Dict (Ob k b)
  default tgt :: (Ob k ~ Trivial k) => k a b -> Dict (Ob k b)
  tgt _ = Dict

  op :: k a b -> Op k b a
  default op :: (Op k ~ Y k) => k a b -> Op k b a
  op = Y

  unop :: Op k b a -> k a b
  default unop :: (Op k ~ Y k) => Op k b a -> k a b
  unop (Y f) = f

newtype Y k a b = Y (k b a)

instance (Category k, Op k ~ Y k) => Category (Y k) where
  type Op (Y k) = k
  type Ob (Y k) = Ob k
  id = Y id
  Y f . Y g = Y (g . f)
  src (Y f) = tgt f
  tgt (Y f) = src f
  op (Y f) = f
  unop = Y

instance Category (:-)

instance Category (->)

instance Category (:~:) where
  type Op (:~:) = (:~:)
  op = Eq.sym
  unop = Eq.sym

instance Category Coercion where
  type Op Coercion = Coercion
  op = Co.sym
  unop = Co.sym
