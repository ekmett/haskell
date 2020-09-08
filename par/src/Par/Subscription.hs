{-# Language DerivingVia #-}
module Par.Subscription where

import Data.Monoid
import Par.Monad

newtype Subscription = Subscription { cancel :: Par () }
  deriving (Semigroup, Monoid) via Ap Par ()
