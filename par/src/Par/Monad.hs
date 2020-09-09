{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language DerivingVia #-}
{-# Language OverloadedLists #-}
{-# Language RecordWildCards #-}
{-# Language TypeFamilies #-}
module Par.Monad where

import Control.Concurrent
import Control.Exception hiding (mask_)
import Control.Monad (join, when)
import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.Trans.Cont
import Control.Monad.Primitive
import Data.IORef
import Data.Foldable
import Data.Primitive.Array
import Data.Traversable (for)
import Par.Counted
import Par.Deque as Deque
import Par.Exception
import Par.Fiber
import System.Random.MWC as MWC

newtype Par a = Par { unPar :: (a -> Fiber ()) -> Fiber () }
  deriving 
  ( Functor
  , Applicative
  , Monad
  , MonadThrow
  , MonadIO
  ) via ContT () Fiber

instance PrimMonad Par where
  type PrimState Par = RealWorld
  primitive m = Par \k -> primitive m >>= k

fork :: Par a -> Par ()
fork m = Par \k -> do
  defer $ k ()
  unPar m \_ -> schedule

--interleave :: Par a -> Par a 
--interleave m = Par \k -> do
  
(<$!>) :: Monad m => (a -> b) -> m a -> m b
f <$!> m = do
  v <- m
  pure $! f v

infixl 4 <$!>

runPar_ :: Par a -> IO ()
runPar_ (Par m) = do
  idlers <- newIORef []
  n <- getNumCapabilities
  tid <- myThreadId
  (k,_) <- threadCapability tid
  ws <- for [0..n-1] \ident -> do
    pool <- Deque.empty
    seed <- MWC.create
    karma <- newIORef 0
    workers <- newArray (n-1) (fail "PANIC! runPar_ missing worker")
    return (Worker {..}, steal pool)
  let iws = init ws
      lws = last ws
  forM_ ws \(i,_) -> forM_ iws \(j,s) -> writeArray (workers i) (ident j) s
  forM_ iws \(i,_) -> do
    writeArray (workers i) (ident i) (snd lws)
    forkOn (k + 1 + ident i) (runFiber schedule i)
  let ks = karma . fst <$!> ws
  runFiber (m \_ -> schedule) (fst lws)
  d <- foldlM (\x i -> do y <- readIORef i; return $! x + y) 0 ks
  when (d < 0) $ throwIO BlockedIndefinitelyOnIVar

runPar :: Par a -> IO a
runPar m = do
  r <- newEmptyMVar
  runPar_ do
     a <- m
     liftIO $ putMVar r a
  readMVar r

newtype IVar a = IVar (IORef (Either a (Counted (a -> Fiber ()))))

newIVar :: Par (IVar a)
newIVar = liftIO $ IVar <$> newIORef (Right [])

readIVar :: IVar a -> Par a
readIVar (IVar r) = Par $ \k -> mask_ $ join $ liftIO $ atomicModifyIORef' r $ \case
  l@(Left a) -> (l, k a)
  Right ks   -> (Right (k:+ks), addKarma (-1) >> schedule)

writeIVar :: Eq a => IVar a -> a -> Par ()
writeIVar (IVar r) a = Par $ \k -> mask_ $ join $ liftIO $ atomicModifyIORef' r $ \case
  l@(Left b)
    | a == b    -> (l, k ())
    | otherwise -> (l, liftIO $ throwM Contradiction)
  Right ks      -> (Left a, do for_ ks (\k' -> defer $ k' a); addKarma (length ks); k () )

unsafeWriteIVar :: IVar a -> a -> Par ()
unsafeWriteIVar (IVar r) a = Par $ \k  -> mask_ $ join $ liftIO $ atomicModifyIORef' r $ \case
  l@Left{} -> (l, k ())
  Right ks -> (Left a, do for_ ks (\k' -> defer $ k' a); addKarma (length ks); k () )

(|*|) :: Par (a -> b) -> Par a -> Par b
pf |*| pa = do
  ra <- newIVar
  fork do
    a <- pa
    unsafeWriteIVar ra a
  f <- pf
  f <$> readIVar ra

infixl 4 |*|
