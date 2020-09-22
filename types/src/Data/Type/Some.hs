{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}
{-# language MagicHash #-}

-- parametric colimits

module Data.Type.Some 
  ( Some(Some)
  , toSS
  , fromSS
  , fromSC
  , toSC
  , rightSC
  , leftSC
  ) where

import Control.Applicative
import Data.Type.Internal
import Data.Some

fromSS :: Some (SingT @a) -> a
fromSS (Some (Sing a)) = a
{-# inline fromSS #-}

toSS :: a -> Some (SingT @a)
toSS a = Some (SING a)
{-# inline toSS #-}

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
