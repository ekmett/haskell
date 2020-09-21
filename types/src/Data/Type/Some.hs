{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}

-- parametric colimits

module Data.Type.Some 
  ( Some(Some)
  , singSome
  , someSing
  , fromSC
  , toSC
  , rightSC
  , leftSC
  ) where

import Control.Applicative
import Data.Type.Internal
import Data.Some

someSing :: Some (Sing @a) -> a
someSing (Some (Sing a)) = a
{-# inline someSing #-}

singSome :: a -> Some (Sing @a)
singSome a = Some (SING a)
{-# inline singSome #-}

type f ~> g = forall i. f i -> g i
infixr 0 ~>

fromSC :: Some (Const a) -> a
fromSC (Some (Const a)) = a

toSC :: a -> Some (Const a)
toSC a = Some (Const a)

rightSC :: (Some f -> x) -> f ~> Const x
rightSC k = Const . k . Some

leftSC :: (f ~> Const x) -> Some f -> x
leftSC k (Some f) = getConst (k f)
