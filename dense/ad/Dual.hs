{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language ConstraintKinds #-}

module Dual 
  ( Scalar(..)
  , ScalarType
  , IsKnownZero
  , isKnownZero
  ) where

import GHC.Types
import qualified Scalar as Primal

type family Snd (p :: (Type,b)) :: b where
  Snd '(a,b) = b

type Primal s = Primal.Scalar (Snd s)

type ScalarType = (Type, Primal.ScalarType)
data Scalar (s :: ScalarType)
  = Dual { primal :: Primal s, tangent :: Primal s }

instance Num (Primal s) => Num (Scalar s) where
  Dual a a' - Dual b b' = Dual (a - b) (a' - b')
  Dual a a' + Dual b b' = Dual (a + b) (a' + b')
  Dual a a' * Dual b b' = Dual (a * b) (a' * b + b' * a)
  abs (Dual a a') = Dual (abs a) (a' * signum a)
  negate (Dual a a') = Dual (negate a) (negate a')
  signum (Dual a _) = Dual (signum a) 0
  fromInteger n = Dual (fromInteger n) 0

instance Fractional (Primal s) => Fractional (Scalar s) where
  Dual u u' / Dual v v' = Dual (u / v) ((u'*v - u*v') / (v*v))
  recip (Dual u u') = Dual (recip u) (negate u' / (u*u))
  fromRational n = Dual (fromRational n) 0

type IsKnownZero (s :: (Type, Primal.ScalarType)) = Primal.IsKnownZero (Snd s)

isKnownZero :: IsKnownZero s => Scalar s -> Bool
isKnownZero (Dual a a') = Primal.isKnownZero a && Primal.isKnownZero a'
