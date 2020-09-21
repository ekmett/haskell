{-# Language BangPatterns #-}
{-# Language MagicHash #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Data.Eq.Strict 
  ( StrictEq
  , withPtrEq
  ) where

import Data.Type.Internal
import GHC.Exts

withPtrEq :: StrictEq a => a -> a -> Bool
withPtrEq a b
   = isTrue# (reallyUnsafePtrEquality# a b)
  || a == b
