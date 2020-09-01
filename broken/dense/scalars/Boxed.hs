{-# language KindSignatures #-}
{-# language TypeFamilies #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ConstraintKinds #-}
module Known 
  ( ScalarType
  , Scalar
  , IsKnownZero
  , isKnownZero
  ) where

import GHC.Types

type ScalarType = Type
newtype Scalar (s :: Type) = ScalarKnown s
  deriving newtype (Eq,Ord,Show,Num,Floating,Fractional,Enum,Real,RealFloat,RealFrac,Bounded,Integral)

type IsKnownZero s = (Num s, Eq s)

isKnownZero :: IsKnownZero s => Scalar s -> Bool
isKnownZero s = s == 0
{-# inline isKnownZero #-}
