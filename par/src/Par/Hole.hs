{-# Language MagicHash #-}
{-# Language ForeignFunctionInterface #-}
{-# Language UnboxedTuples #-}
{-# Language UnliftedFFITypes #-}
{-# Language BangPatterns #-}
{-# Language GHCForeignImportPrim #-}

-- | Based on <http://www.twanvl.nl/blog/haskell/unsafe-sequence>
module Par.Hole 
  ( newHole
  , setHole
  , unsafeSetField
  ) where

import GHC.Types
import GHC.Prim

foreign import prim "newHolezh" newHole# :: Int# -> (# Any #)
foreign import prim "setHolezh" setHole# :: Any -> Any -> (##)
foreign import prim "unsafeSetFieldzh" unsafeSetField# :: Int# -> Any -> Any -> (##)

-- | Allocate a value that can be overwritten *once* with 'setHole'.
newHole :: IO a
newHole = case newHole# 0# of
  (# x #) -> pure (unsafeCoerce# x)
{-# INLINEABLE newHole #-}

-- | Set the value of something allocated with 'newHole'
setHole :: a -> a -> IO ()
setHole x y = case setHole# (unsafeCoerce# x :: Any) (unsafeCoerce# y :: Any) of
  (##) -> pure ()
{-# INLINEABLE setHole #-}

unsafeSetField :: Int -> a -> b -> IO ()
unsafeSetField (I# i) !x y =
  case unsafeSetField# i (unsafeCoerce# x :: Any) (unsafeCoerce# y :: Any) of
    (##) -> pure ()
{-# INLINEABLE unsafeSetField #-}
