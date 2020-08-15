{-# language KindSignatures #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language ConstraintKinds #-}
module Float 
  ( ScalarType
  , Scalar(..)
  , IsKnownZero
  , isKnownZero
  ) where

import GHC.Types

type ScalarType = ()
newtype Scalar (s :: ScalarType) = ScalarFloat Float
  deriving newtype (Eq,Ord,Show,Num,Floating,Fractional,Real,RealFloat,RealFrac)

type family IsKnownZero (s :: ScalarType)
type instance IsKnownZero s = () :: Constraint

isKnownZero :: IsKnownZero s => Scalar s -> Bool
isKnownZero s = 0 == s
{-# inline isKnownZero #-}
