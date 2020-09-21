{-# language StandaloneKindSignatures #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language TemplateHaskell #-}

module Vec where

import Data.Type
import Numeric.Natural

type Vec :: Type -> Natural -> Type
type role Vec representational nominal
data Vec a n where
  VNil  :: Vec a Z
  VCons :: a -> !(Vec a n) -> Vec a (S n)

makeSing ''Vec
