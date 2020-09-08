{-# Language BangPatterns #-}
{-# Language BlockArguments #-}
{-# Language ForeignFunctionInterface #-}
{-# Language GHCForeignImportPrim #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language UnliftedFFITypes #-}

-- | Based on <http://www.twanvl.nl/blog/haskell/unsafe-sequence>
module Par.Hole 
  ( newHole
  , setHole
  , unsafeSetField
  , unsafeGetField
  , sequenceIO
  , sequenceUnliftIO
  , sequenceH
  ) where

import Control.Monad.IO.Unlift
import GHC.Types
import GHC.Prim

foreign import prim "newHolezh" newHole# :: Int# -> (# Any #)
foreign import prim "setHolezh" setHole# :: Any -> Any -> (##)
foreign import prim "unsafeSetFieldzh" unsafeSetField# :: Int# -> Any -> Any -> (##)
foreign import prim "unsafeGetFieldzh" unsafeGetField# :: Int# -> Any -> (# Any #)

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

unsafeGetField :: Int -> a -> IO b
unsafeGetField (I# i) !x = case unsafeGetField# i (unsafeCoerce# x :: Any) of
  (# y #) -> return (unsafeCoerce# y)
{-# INLINEABLE unsafeGetField #-}

sequenceUnliftIO :: MonadUnliftIO m => [m a] -> m [a]
sequenceUnliftIO [] = pure []
sequenceUnliftIO (mx0:xs0) = withRunInIO \run -> do
    x0 <- run mx0
    let front = x0:[]
    front <$ go run front xs0
  where
    go run back (mx:xs) = do
      x <- run mx
      let back' = x:[]
      unsafeSetField 1 back back'
      go run back' xs
    go _ _ [] = pure ()
{-# INLINEABLE sequenceUnliftIO #-}

sequenceIO :: [IO a] -> IO [a]
sequenceIO [] = pure []
sequenceIO (mx0:xs0) = do
    x0 <- mx0
    let front = x0:[]
    front <$ go front xs0
  where
    go back (mx:xs) = do
      x <- mx
      let back' = x:[]
      unsafeSetField 1 back back'
      go back' xs
    go _ [] = pure ()
{-# INLINEABLE sequenceIO #-}

-- Sequence implemented in terms of holes
sequenceH :: [IO a] -> IO [a]
sequenceH xs0 = do
    front <- newHole
    go front xs0
    return front
  where
  go back [] = setHole back []
  go back (mx:xs) = do
    x <- mx
    back' <- newHole
    setHole back (x:back')
    go back' xs
{-# INLINEABLE sequenceH #-}
