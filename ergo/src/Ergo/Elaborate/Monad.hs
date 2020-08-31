{-# Language BlockArguments #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language UndecidableInstances #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

module Ergo.Elaborate.Monad where

import Control.Applicative (liftA2)
import Control.Monad.Catch
import Control.Monad.Primitive
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.Coerce

newtype M s a = M { unM :: ST s a }
  deriving newtype (Functor,Applicative,Monad,MonadFail,MonadThrow)

unsafeIOToM :: forall s a. IO a -> M s a
unsafeIOToM = coerce (unsafeIOToST :: IO a -> ST s a)
{-# inline unsafeIOToM #-}

unsafeMToIO :: forall s a. M s a -> IO a
unsafeMToIO = coerce (unsafeSTToIO :: ST s a -> IO a)
{-# inline unsafeMToIO #-}

unsafeInterleaveM :: M s a -> M s a
unsafeInterleaveM (M m) = M (unsafeInterleaveST m)

instance PrimMonad (M s) where
  type PrimState (M s) = s
  primitive k = M (primitive k)
  {-# inline primitive #-}

instance PrimBase (M s) where
  internal (M m) s = internal m s
  {-# inline internal #-}

instance MonadCatch (M s) where
  catch m k = unsafeIOToM $ catch (unsafeMToIO m) \e -> unsafeMToIO (k e)
  {-# inline catch #-}

instance MonadMask (M s) where
  mask k = unsafeIOToM $ mask 
    \ma2ma -> unsafeMToIO $ k \ma -> unsafeIOToM $ ma2ma $ unsafeMToIO ma
  {-# inline mask #-}
  uninterruptibleMask k = unsafeIOToM $ uninterruptibleMask 
    \ma2ma -> unsafeMToIO $ k \ma -> unsafeIOToM $ ma2ma $ unsafeMToIO ma
  {-# inline uninterruptibleMask #-}
  generalBracket ma f g = unsafeIOToM $ generalBracket 
    (unsafeMToIO ma) 
    (\ a eb -> unsafeMToIO $ f a eb) 
    (\a -> unsafeMToIO $ g a)
  {-# inline generalBracket #-}

instance Semigroup a => Semigroup (M s a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (M s a) where
  mempty = pure mempty

runM :: (forall s. M s a) -> a
runM m = runST (unM m)
{-# inline runM #-}
