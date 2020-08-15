{-# language StandaloneDeriving #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language MonoLocalBinds #-}
{-# language PatternSynonyms #-}
{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language TypeFamilies #-}
module V2 
  ( Vector(V2,V2_)
  , VectorType
  , Scalar
  , ScalarType
  ) where

import Control.Lens
import qualified Scalar
import Vector.Class

-- can use this module as a scalar type in its own right
type ScalarType = Scalar.ScalarType
type Scalar s = Vector s
type VectorType = Scalar.ScalarType

data Vector (s :: VectorType) = V2_
  {-# unpack #-} !(Scalar s)
  {-# unpack #-} !(Scalar s)

-- {-# complete V2 :: Vector #-} complete pragmas suck, i can't supply this, really?

deriving instance Eq (Scalar s) => Eq (Vector s)
deriving instance Ord (Scalar s) => Ord (Vector s)
deriving instance Read (Scalar s) => Read (Vector s)
deriving instance Show (Scalar s) => Show (Vector s)

type instance Elem Vector s = Scalar s

instance IsV2 Vector where
  _V2 = iso (\(V2_ a b) -> (a,b)) (\(a,b) -> (V2_ a b))
  {-# inline _V2 #-}

-- now to add most of the instances from linear

instance IsVector Vector where
  vector f (V2_ a b) = V2_ <$> f a <*> f b
