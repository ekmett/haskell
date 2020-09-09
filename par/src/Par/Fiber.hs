{-# Language LambdaCase #-}
{-# Language RecordWildCards #-}
{-# Language NamedFieldPuns #-}
{-# Language TypeFamilies #-}
{-# Language BlockArguments #-}
{-# Language OverloadedLists #-}
{-# Language DerivingVia #-}
module Par.Fiber where

import Control.Concurrent.MVar
import Control.Monad (join, when, unless)
import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.IO.Unlift
import Control.Monad.Primitive
import Control.Monad.Trans.Reader
import Data.Foldable
import Data.IORef
import Data.Maybe
import Data.Primitive.Array
import Par.Counted
import Par.Deque as Deque
import System.Random.MWC
import Data.Atomics.Counter

-- internal state of a Worker
data Worker = Worker
  { ident   :: {-# UNPACK #-} !Int
  , pool    :: !(Deque (Fiber ()))
  , peers   :: {-# UNPACK #-} !(MutableArray RealWorld (IO (Maybe (Fiber ()))))
  , idlers  :: {-# UNPACK #-} !(IORef (Counted (MVar (Fiber ()))))
  , seed    :: {-# UNPACK #-} !(Gen RealWorld)
  , karma   :: {-# UNPACK #-} !AtomicCounter
  }

-- TODO: change peers to just contain an IO action that can do stealing. This prevents us from holding the entire other worker alive and makes a safer back-end.

newtype Fiber a = Fiber { runFiber :: Worker -> IO a }
  deriving 
    ( Functor, Applicative, Monad, MonadFail
    , MonadThrow, MonadCatch, MonadMask
    , MonadIO
    , MonadUnliftIO
    ) via ReaderT Worker IO

instance PrimMonad Fiber where
  type PrimState Fiber = RealWorld
  primitive f = Fiber \_ -> primitive f

-- | Look for something to do locally, otherwise go look for work
schedule :: Fiber ()
schedule = Fiber \ s@Worker{..} -> pop pool >>= \case
  Just t -> do
    runFiber t s
  Nothing 
    | n <- sizeofMutableArray peers -> 
      when (n > 0) do
        runFiber (interview (n-1)) s

-- | Go door to door randomly looking for work. Requires there to be at least one door to knock on.
interview :: Int -> Fiber ()
interview i
  | i > 0 = Fiber \s@Worker{peers, seed} -> do
    j <- uniformR (0,i) seed -- perform an on-line Knuth shuffle step
    a <- readArray peers i
    b <- readArray peers j
    writeArray peers i b
    writeArray peers j a
    m <- liftIO b
    runFiber (fromMaybe (interview (i-1)) m) s
  | otherwise = Fiber \s@Worker{peers} -> do
    b <- readArray peers 0
    m <- liftIO b
    runFiber (fromMaybe idle m) s

-- | We have a hot tip from somebody with a job opening!
referral :: IO (Maybe (Fiber ())) -> Fiber ()
referral b = liftIO b >>= fromMaybe schedule

-- | Give up and wait for somebody to wake us up.
idle :: Fiber ()
idle = Fiber \s@Worker{..} -> do
  m <- newEmptyMVar
  is <- atomicModifyIORef idlers \is -> (m :+ is,is)
  if length is == sizeofMutableArray peers
  then for_ is \i -> putMVar i $ pure () -- shut it down. we're the last idler.
  else do
    t <- takeMVar m -- We were given this, we didn't steal it. Really!
    runFiber t s

-- | Spawn a background task. We first put it into our job queue, and then we wake up an idler if there are any and have them try to steal it.
defer :: Fiber () -> Fiber ()
defer t = Fiber \Worker{idlers,pool} -> do
  xs <- readIORef idlers
  push t pool
  unless (Prelude.null xs) $
    join $ atomicModifyIORef idlers \case
       i:+is -> (is, putMVar i $ referral $ steal pool)
       _     -> ([], return ())

-- | If the computation ends and we have globally accumulated negative karma then somebody, somewhere, is blocked.
addKarma :: Int -> Fiber ()
addKarma k = Fiber \ Worker{karma} -> incrCounter_ k karma
