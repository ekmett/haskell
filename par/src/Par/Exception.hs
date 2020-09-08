{-# LANGUAGE DeriveAnyClass #-}
module Par.Exception where

import Control.Exception

data BlockedIndefinitelyOnIVar = BlockedIndefinitelyOnIVar 
  deriving (Show, Exception)

data Contradiction = Contradiction
  deriving (Show,Exception)
