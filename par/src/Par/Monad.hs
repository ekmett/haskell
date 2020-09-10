{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language DerivingVia #-}
{-# Language OverloadedLists #-}
{-# Language RecordWildCards #-}
{-# Language TupleSections #-}
{-# Language TypeFamilies #-}
module Par.Monad where

import Control.Concurrent
import Control.Exception hiding (mask_)
import Control.Monad (join, when)
import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.Trans.Cont
import Control.Monad.Primitive
import Data.Atomics.Counter
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
    karma <- newCounter 0
    peers <- newArray (n-1) (fail "PANIC! runPar_ missing worker")
    return (Worker {..}, steal pool)
  let iws = init ws
      (lw,ls) = last ws
  for_ ws \(i,_) ->
    for_ iws \(j,s) ->
      writeArray (peers i) (ident j) s
  for_ iws \(i,_) -> do
    writeArray (peers i) (ident i) ls
    forkOn (k + 1 + ident i) do
      runFiber schedule i
  runFiber (m \_ -> schedule) lw
  karma <- foldlM (\x (w,_) -> (x +) <$!> readCounter (karma w)) 0 ws
  when (karma < 0) $ throwIO BlockedIndefinitelyOnIVar

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
readIVar (IVar r) = Par \k -> mask_ $ join $ liftIO $ atomicModifyIORef' r \case
  l@(Left a) -> (l, k a)
  Right ks   -> (Right (k:+ks),) do
    addKarma (-1)
    schedule

writeIVar :: Eq a => IVar a -> a -> Par ()
writeIVar (IVar r) a = Par \k -> mask_ $ join $ liftIO $ atomicModifyIORef' r \case
  l@(Left b)
    | a == b    -> (l, k ())
    | otherwise -> (l, throwM Contradiction)
  Right ks      -> (Left a,) do
    for_ ks \k' -> defer $ k' a
    addKarma (length ks)
    k ()

unsafeWriteIVar :: IVar a -> a -> Par ()
unsafeWriteIVar (IVar r) a = Par \k  -> mask_ $ join $ liftIO $ atomicModifyIORef' r \case
  l@Left{} -> (l, k ())
  Right ks -> (Left a,) do
    for_ ks \k' -> defer $ k' a
    addKarma (length ks)
    k ()

(|*|) :: Par (a -> b) -> Par a -> Par b
pf |*| pa = do
  ra <- newIVar
  fork do
    a <- pa
    unsafeWriteIVar ra a
  f <- pf
  f <$> readIVar ra

{-
(*|) :: Par a -> Par b -> Par b
pa *| pb = do
  fork pa
  pb
(|*) :: Par a -> Par b -> Par a
pa |* pb = do
  fork pb
  pa

infixl 4 |*|

newtype Conc a = Conc { runConc :: Par a }
  deriving Functor

instance Applicative Conc where
  pure a = Conc (pure a)
  Conc p <*> Conc q = Conc (p |*| q)
  Conc p  *> Conc q = Conc (p  *| q)
  Conc p <*  Conc q = Conc (p |*  q)
-}
