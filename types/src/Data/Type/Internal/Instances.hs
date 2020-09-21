{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_HADDOCK not-home #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Internal.Instances where

import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Proxy
import Data.Type.Internal.TH

makeSing ''Either
makeSing ''Maybe
makeSing ''Bool
makeSing ''Ordering
makeSing ''Const
makeSing ''Compose
makeSing ''Identity
makeSing ''Proxy
