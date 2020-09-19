{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}

module Data.Type
  ( Sing
    ( Sing
    , fromSing

    -- singleton nats
    , SZ
    , SS

    -- singleton ints
    , SIntZ
    , SIntS
    , SMkInt

    -- singleton lists
    , SNil
    , SCons

    -- singleton Maybe
    , SNothing
    , SJust

    -- singleton products
    , SPair

    -- singleton booleans
    , SFalse
    , STrue

    -- singleton ordering
    , SLT
    , SEQ
    , SGT

    -- singleton sums
   -- , SLeft
   -- , SRight
    )
  , SEq
  , SingI(sing)
  , Reifies, ify, reify, reflect

  -- lowering types
  , type Type
  , pattern Type -- sadly I can't use Type(Type) because reasons
  , pattern SType

  -- lowering nats
  , type Nat
  , pattern Nat
  , pattern Z
  , pattern S
  , type Z
  , type S

  -- lowering symbols
  , Symbol(Symbol)

  -- lifting ints
  , type MkInt
  -- lifting chars
  , type MkChar
  ) where

import Data.Type.Internal
import Data.Kind (Type)
import GHC.TypeLits (Nat, Symbol)

