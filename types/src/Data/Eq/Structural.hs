{-# Language BangPatterns #-}
{-# Language MagicHash #-}
module Data.Eq.Structural 
  ( SEq
  , withPtrEq
  ) where

import Data.Type.Internal
import GHC.Exts

withPtrEq :: SEq a => a -> a -> Bool
withPtrEq a b
   = isTrue# (reallyUnsafePtrEquality# a b)
  || a == b
