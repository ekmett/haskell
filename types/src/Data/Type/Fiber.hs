{-# language BlockArguments #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language MagicHash #-}
{-# language LambdaCase #-}
{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneKindSignatures #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}

module Data.Type.Fiber 
  ( type (->#)(..)
  , unarr
  ) where

import Control.Arrow
import Control.Category
import Data.Kind
import Data.Type.Internal
import Data.Type.Internal.Instances
import Data.Type.Some
import GHC.Exts
import Prelude hiding (id,(.))

type (->#) :: Type -> Type -> Type
type role (->#) nominal nominal
data a -># b where
  Fiber :: forall a b. { runFiber :: (forall (i::a). Sing i -> Some (SingT @b)) } -> a -># b
infixr 0 ->#

instance Category (->#) where
  id = Fiber Some
  Fiber f . Fiber g = Fiber \si -> case g si of
    Some sj -> f sj

unarr :: forall (a :: Type) (b :: Type). (a -># b) -> a -> b
unarr (Fiber f) (x::a) = reify x \(_ :: Proxy# i) -> case f (sing @a @i) of
  Some (Sing b) -> b

instance Arrow (->#) where
  arr f = Fiber \x -> toSS $ f $ fromSing x
  first f = Fiber \case
    STuple2 x y -> case runFiber f x of
      Some x' -> Some $ STuple2 x' y
  second f = Fiber \case
    STuple2 x y -> case runFiber f y of
      Some y' -> Some $ STuple2 x y'
  f *** g = Fiber \case
    STuple2 x y -> case runFiber f x of
      Some x' -> case runFiber g y of
        Some y' -> Some $ STuple2 x' y'
  f &&& g = Fiber \x -> 
    case runFiber f x of
      Some y -> case runFiber g x of
        Some z -> Some $ STuple2 y z

instance ArrowChoice (->#) where
  left f = Fiber \case
    SLeft a -> case runFiber f a of
      Some a' -> Some (SLeft a')
    SRight b -> Some $ SRight b
  right f = Fiber \case
    SLeft a -> Some $ SLeft a
    SRight b -> case runFiber f b of
      Some b' -> Some (SRight b')
  f +++ g = Fiber \case
    SLeft a -> case runFiber f a of
      Some a' -> Some (SLeft a')
    SRight b -> case runFiber g b of
      Some b' -> Some (SRight b')
    
instance ArrowApply (->#) where
  app = Fiber \case
    STuple2 f x -> runFiber (fromSing f) x

instance ArrowLoop (->#) where
  loop f = arr $ loop (unarr f)
