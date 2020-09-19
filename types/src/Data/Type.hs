{-# language PatternSynonyms #-}
{-# language ExplicitNamespaces #-}
{-# language TemplateHaskell #-}
{-# language StandaloneKindSignatures #-}
{-# language DataKinds #-}
{-# language PolyKinds #-}
{-# language RoleAnnotations #-}
{-# language ViewPatterns #-}
{-# language GADTs #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Type
  ( Sing
    ( Sing
    , fromSing
    , SS, SZ -- Nat
    , SType -- Type
    , SIntS, SIntZ, SMkInt -- Int
    , SLeft, SRight -- Either
    , SJust, SNothing -- Maybe
    , SNil, SCons -- List
    , STrue, SFalse -- Bool
    , SLT, SEQ, SGT -- Ordering
    , SPair -- (,)
    )
  , SEq
  , SingI(..)
  , Reifies, ify , reify, reflect
  -- lowering types
  , type Type
  , pattern Type
  -- lowering nats
  , Nat
  , toNat, fromNat
  , pattern Nat
  , pattern Z
  , pattern S
  , type Z
  , type S
  -- lowering symbols
  , Symbol
  , pattern Symbol
  , toSymbol
  , fromSymbol
  -- lifting ints
  , MkInt
  -- lifting chars
  , MkChar
  ) where

import Data.Type.Internal
  hiding (safePred) 
import Data.Type.TH
import Data.Kind (Type)
import GHC.TypeLits (Nat, Symbol)

makeSing ''Either
makeSing ''Maybe
makeSing ''Bool
makeSing ''Ordering
