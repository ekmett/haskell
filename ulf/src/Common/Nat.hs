{-# Language ExplicitNamespaces #-}

module Common.Nat
  ( ToInt(..)
  , type Z
  , type S
  , wk, wk2
  , N(NZ,NS)
  , Fin(Z,S)
  ) where

import Common.Internal.Nat
