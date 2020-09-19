{-# Language Unsafe #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Type.Unsafe
  ( Sing(..)
  , FromNat
  , FromSymbol
  ) where

import Data.Type.Internal
import Data.Type ()
