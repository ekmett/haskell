{-# language KindSignatures #-}
{-# language TypeFamilies #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ConstraintKinds #-}
module Unknown
  ( ScalarType
  , Scalar
  , IsKnownZero
  , isKnownZero
  ) where

import GHC.Types

type ScalarType = Type
newtype Scalar (s :: Type) = ScalarUnknown s
  deriving newtype (Eq,Ord,Show,Num,Floating,Fractional,Enum,Real,RealFloat,RealFrac,Bounded,Integral)

type IsKnownZero s = () :: Constraint

isKnownZero :: IsKnownZero s => Scalar s -> Bool
isKnownZero _ = False
{-# inline isKnownZero #-}
