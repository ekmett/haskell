{-# language RankNTypes #-}
{-# language TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language PolyKinds #-}
module Vector.Class
  ( type Elem
  , IsV2(..)
  , pattern V2
  , IsVector(..)
  ) where

import GHC.Types

import Control.Lens

type family Elem (t :: k -> Type) (s :: k) :: Type

class IsV2 t where
  _V2 :: Iso (t s) (t s') (Elem t s, Elem t s) (Elem t s', Elem t s')

pattern V2 :: IsV2 t => Elem t s -> Elem t s -> t s
pattern V2 a b <- (view _V2 -> (a, b)) where
  V2 a b = _V2 # (a, b)

-- {-# complete V2 #-} -- can't supply this here because complete pragmas suck

class IsVector t where
  vector :: Traversal (t s) (t s') (Elem t s) (Elem t s')
