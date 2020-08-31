{-# Language CPP #-}
{-# Language DeriveFunctor #-}
{-# Language DeriveFoldable #-}
{-# Language FlexibleContexts #-}
{-# Language DeriveTraversable #-}
{-# Language FlexibleInstances #-}
{-# Language DeriveDataTypeable #-}
{-# Language UndecidableInstances #-}
{-# Language MultiParamTypeClasses #-}

-- |
-- Copyright :  (c) Edward Kmett and Dan Doel 2012-2013
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- These combinators can be used to retain sharing information.

module Control.Monad.Sharing
  ( runSharing
  , withSharing
  , sharing
  , SharingT(..)
  , Shared(..)
  , uncaring
  ) where

import Control.Monad (void)
import Control.Monad.Writer.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Comonad
import Data.Monoid
import Data.Data

data Shared a = Shared !Bool a
  deriving (Eq,Ord,Show,Read,Functor,Foldable,Traversable,Data)

instance Comonad Shared where
  extract (Shared _ a) = a
  extend f s@(Shared b _) = Shared b (f s)

-- An efficient strict-in-the-monoid version of WriterT Any@
newtype SharingT m a = SharingT { unsharingT :: m (Shared a) }

instance Monad m => Functor (SharingT m) where
  fmap f (SharingT m) = SharingT $ do
    Shared p a <- m
    return $! Shared p (f a)
  {-# inline fmap #-}

instance Monad m => Applicative (SharingT m) where
  pure a = SharingT (return (Shared False a))
  {-# inline pure #-}
  SharingT mf <*> SharingT ma = SharingT $ do
    Shared p f <- mf
    Shared q a <- ma
    return $! Shared (p || q) (f a)
  {-# inline (<*>) #-}

instance Monad m => Monad (SharingT m) where
  return a = SharingT (return (Shared False a))
  {-# inline return #-}
  SharingT m >>= f = SharingT $ do
    Shared p a <- m
    Shared q b <- unsharingT (f a)
    return $! Shared (p || q) b
  {-# inline (>>=) #-}

instance Monad m => MonadWriter Any (SharingT m) where
  tell (Any p) = SharingT $ return $ Shared p ()
  {-# inline tell #-}
  listen (SharingT ma) = SharingT $ do
    Shared p a <- ma
    return $! Shared p (a, Any p)
  {-# inline listen #-}
  pass (SharingT mapp) = SharingT $ do
    Shared p (a, pp) <- mapp
    return $! Shared (getAny (pp (Any p))) a
  {-# inline pass #-}

instance MonadTrans SharingT where
  lift ma = SharingT $ do
    a <- ma
    return $! Shared False a
  {-# inline lift #-}

instance MonadIO m => MonadIO (SharingT m) where
  liftIO = lift . liftIO
  {-# inline liftIO #-}

instance MonadState s m => MonadState s (SharingT m) where
  get = lift get
  {-# inline get #-}
  put = lift . put
  {-# inline put #-}

instance MonadReader e m => MonadReader e (SharingT m) where
  ask = lift ask
  {-# inline ask #-}
  local f = SharingT . local f . unsharingT
  {-# inline local #-}

-- | Run an action, if it returns @'Any' 'True'@ then use its new value, otherwise use the passed in value.
--
-- This can be used to recover sharing during unification when no interesting unification takes place.
--
-- This version discards the 'SharingT' wrapper.
runSharing :: Monad m => a -> SharingT m a -> m a
runSharing a m = do
  Shared modified b <- unsharingT m
  return $! if modified then b else a
{-# inline runSharing #-}

withSharing :: Monad m => (a -> SharingT m a) -> a -> m a
withSharing k a = runSharing a (k a)
{-# inline withSharing #-}

uncaring :: Functor m => SharingT m a -> m ()
uncaring = void . unsharingT
{-# inline uncaring #-}

-- | Run an action, if it returns @'Any' 'True'@ then use its new value, otherwise use the passed in value.
--
-- This can be used to recover sharing during unification when no interesting unification takes place.
--
-- This version retains the current monad wrapper.
sharing :: MonadWriter Any m => a -> m a -> m a
sharing a m = do
  (b, Any modified) <- listen m
  return $! if modified then b else a
{-# inline sharing #-}
