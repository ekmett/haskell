{-# Language ImportQualifiedPost #-}
module Common.SparseSet
  ( MutableSparseSet
  , new -- O(1)
  , insert -- O(1)
  , delete -- O(1)
  , read -- O(1)
  , write -- O(1)
  , reset -- O(1)
  , unsafeFreezeAndShrink -- O(1)
  , unsafeFreeze -- O(1)
  , unsafeThaw -- O(1)
  , capacity -- O(1)
  , getCount -- O(1)

  , SparseSet
  , count -- O(1)
  , index -- O(1)
  , union -- O(count a + count b)
  , intersection -- O(min (count a) (count b))
  , complement -- O(universe a)
  , difference -- O(count a)
  , Exts.fromList -- O(count) 
  , toList -- O(length)
  , Universe(..) -- O(1)
  ) where

import Common.Internal.SparseSet
import GHC.Exts qualified as Exts
import Prelude hiding (read)
