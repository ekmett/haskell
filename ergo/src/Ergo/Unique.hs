{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language BlockArguments #-}

-- |
-- Copyright :  (c) Edward Kmett 2018-2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Unique 
  ( Unique
  , UniqueM
  , newUnique
  ) where

import Control.Monad.Primitive
import Data.Hashable
import Data.Type.Equality
import GHC.Prim
import GHC.Types
import Unsafe.Coerce

data Unique s = Unique {-# unpack #-} !Int (MutableByteArray# s)
type UniqueM m = Unique (PrimState m)

instance Eq (Unique s) where
  Unique _ p == Unique _ q = isTrue# (sameMutableByteArray# p q)

instance Hashable (Unique s) where
  hash (Unique i _) = i
  hashWithSalt d (Unique i _) = hashWithSalt d i

instance TestEquality Unique where
  testEquality (Unique _ i) (Unique _ j)
    | isTrue# (unsafeCoerce# sameMutableByteArray# i j) = Just (unsafeCoerce Refl)
    | otherwise = Nothing

newUnique :: PrimMonad m => m (UniqueM m)
newUnique = primitive \s -> case newByteArray# 0# s of
  (# s', ba #) -> (# s', Unique (I# (addr2Int# (unsafeCoerce# ba))) ba #)
{-# inline newUnique #-}
