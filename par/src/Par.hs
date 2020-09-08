module Par where

{-
-- internal state of a Worker
data Worker = Worker
  { ident   :: {-# UNPACK #-} !Int
  , pool    :: !(Deque (Fiber ()))
  , workers :: !(MutableArray RealWorld Worker) -- Other Workers. They will get shuffled as we schedule work stealing
  , idlers  :: {-# UNPACK #-} !(IORef (Counted (MVar (Fiber ()))))
  , seed    :: !(Gen RealWorld)
  , karma   :: {-# UNPACK #-} !(IORef Int)
  , fast    :: {-# UNPACK #-} !(IORef Bool)
  }
-}
