{-# language BangPatterns #-}
{-# language MagicHash #-}
module Data.Eq.Structural 
  ( SEq
  , withPtrEq
  ) where

import Control.Applicative
import Control.Concurrent
import Data.IORef
import Data.List.NonEmpty
import Data.Proxy
import Data.STRef
import Data.Void
import Foreign.Ptr
import Foreign.StablePtr
import GHC.Prim
import GHC.Types

-- | A type with structural equality
--
-- @
-- x '==' y ==> f x '==' f y
-- @
class Eq a => SEq a
instance SEq (MVar a)
instance SEq (IORef a)
instance SEq (STRef s a)
instance SEq (Proxy a)
instance SEq ThreadId
instance SEq a => SEq (Const a b)
instance SEq Bool
instance SEq ()
instance SEq Void
instance SEq Ordering
instance SEq a => SEq (Maybe a)
instance (SEq a, SEq b) => SEq (a, b)
instance (SEq a, SEq b) => SEq (Either a b)
instance SEq a => SEq [a]
instance SEq a => SEq (NonEmpty a)
instance SEq (Ptr a)
instance SEq (StablePtr a)

withPtrEq :: SEq a => a -> a -> Bool
withPtrEq !a !b 
   = isTrue# (reallyUnsafePtrEquality# a b) 
  || a == b
