{-# language DeriveTraversable #-}
{-# language TypeFamilies #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedLists #-}

module Relative.Unaligned
  ( View(..) -- re-export
  , Rev(..) -- re-export
  , Cons(..)
  , Uncons(..)
  , Snoc(..)
  , Unsnoc(..)
  , Nil(..)
  , Singleton(..)
  , Q(..)
  , Cat(..)
  , pattern Nil
  , pattern Cons
  , pattern Snoc
  , foldMapQ
  , foldMapCat
  ) where

import Delta
import Data.Default
import Data.Monoid (Dual(..))
import GHC.Exts as Exts
import Relative
import Unaligned.Internal (View(..), Rev(..))

--------------------------------------------------------------------------------
-- * Interface
--------------------------------------------------------------------------------

-- TODO: use Control.Lens.Cons?
class Cons t where
  cons :: Relative a => a -> t a -> t a

class Nil t where
  nil :: Relative a => t a

class Uncons t where
  uncons :: Relative a => t a -> View a (t a)

class Unsnoc t where
  unsnoc :: Relative a => t a -> View (t a) a

class Snoc t where
  snoc :: Relative a => t a -> a -> t a

class Singleton t where
  singleton :: Relative a => a -> t a

pattern Nil :: (Nil t, Uncons t, Relative a) => t a
pattern Nil <- (uncons -> Empty) where
  Nil = nil

pattern Cons :: (Cons t, Uncons t, Relative a) => a -> t a -> t a
pattern Cons a as <- (uncons -> a :&: as) where
  Cons a as = cons a as

pattern Snoc :: (Snoc t, Unsnoc t, Relative a) => t a -> a -> t a
pattern Snoc as a <- (unsnoc -> as :&: a) where
  Snoc as a = snoc as a

--------------------------------------------------------------------------------
-- Reversing containers
--------------------------------------------------------------------------------

instance Nil t => Nil (Rev t) where
  nil = Rev nil

instance Cons t => Snoc (Rev t) where
  snoc (Rev t) f = Rev (cons f t)

instance Uncons t => Unsnoc (Rev t) where
  unsnoc (Rev t) = case uncons t of
    l :&: r -> Rev r :&: l
    Empty -> Empty

instance Unsnoc t => Uncons (Rev t) where
  uncons (Rev t) = case unsnoc t of
    l :&: r -> r :&: Rev l
    Empty -> Empty

instance Snoc t => Cons (Rev t) where
  cons a (Rev b) = Rev (snoc b a)

instance Singleton t => Singleton (Rev t) where
  singleton = Rev . singleton

--------------------------------------------------------------------------------
-- * Lists
--------------------------------------------------------------------------------
data List a = ListCons {-# UNPACK #-} !Delta a (List a) | ListNil

{-# complete Nil, Cons :: List #-}

instance Relative (List a) where
--  rel 0 xs = xs
  rel _ ListNil = ListNil
  rel d (ListCons d' a as) = ListCons (d <> d') a as

instance Nil List where
  nil = ListNil

instance Cons List where
  cons = ListCons mempty

instance Uncons List where
  uncons ListNil = Empty
  uncons (ListCons d a as) = rel d a :&: rel d as

instance Singleton List where
  singleton a = ListCons mempty a Nil

instance Relative a => IsList (List a) where
  type Item (List a) = a
  fromList = foldr cons nil
  fromListN _ = foldr cons nil
  toList = foldMapL pure

foldMapL :: (Relative a, Monoid m) => (a -> m) -> List a -> m
foldMapL f = go mempty where
  go d (ListCons d' a as) = f (rel d'' a) <> go d'' as where d'' = d <> d'
  go _ ListNil = mempty

--------------------------------------------------------------------------------
-- * Queues
--------------------------------------------------------------------------------

data Q a = Q (List a) (Rev List a) (List a)

instance Relative (Q a) where
--  rel 0 xs = xs
  rel d (Q as bs cs) = Q (rel d as) (rel d bs) cs

{-# complete Nil, Cons :: Q #-}

instance Default (Q a) where
  def = Q ListNil (Rev ListNil) ListNil

instance (Show a, Relative a) => Show (Q a) where
  showsPrec d = showsPrec d . Exts.toList

instance Relative a => IsList (Q a) where
  type Item (Q a) = a
  fromList = foldr cons nil
  fromListN _ = foldr cons nil
  toList = foldMapQ pure

foldMapQ :: (Relative a, Monoid m) => (a -> m) -> Q a -> m
foldMapQ f (Q as (Rev bs) _) = foldMapL f as <> getDual (foldMapL (Dual . f) bs)

instance Nil Q where
  nil = Q ListNil (Rev ListNil) ListNil

instance Cons Q where
  cons a (Q f r s) = Q (Cons a f) r (Cons a s)

instance Uncons Q where
  uncons (Q ListNil (Rev ListNil) _) = Empty
  uncons (Q (Cons x f) r s) = x :&: exec f r s
  uncons _ = error "Q.uncons: invariants violated"

instance Singleton Q where
  singleton a = Q [a] (Rev ListNil) ListNil

instance Snoc Q where
  snoc (Q f r s) a = exec f (snoc r a) s

exec :: Relative a => List a -> Rev List a -> List a -> Q a
exec xs ys (ListCons _ _ t) = Q xs ys t
exec xs ys ListNil = Q xs' (Rev ListNil) xs' where xs' = rotate xs ys []

rotate :: Relative a => List a -> Rev List a -> List a -> List a
rotate ListNil (Rev [y]) a = Cons y a
rotate (x `Cons` xs) (Rev (Cons y ys)) a = x `Cons` rotate xs (Rev ys) (Cons y a)
rotate _ _ _ = error "Q.rotate: invariant broken"

--------------------------------------------------------------------------------
-- * Catenable lists
--------------------------------------------------------------------------------

data Cat a = E | C a !(Q (Cat a))

instance Relative a => Relative (Cat a) where
  rel _ E = E
  -- rel 0 as = as
  rel d (C a as) = C (rel d a) (rel d as)

instance Relative a => RelativeSemigroup (Cat a)
instance Relative a => RelativeMonoid (Cat a)

instance (Relative a, Show a) => Show (Cat a) where
  showsPrec d = showsPrec d . Exts.toList

foldMapCat :: (Relative a, Monoid m) => (a -> m) -> Cat a -> m
foldMapCat _ E = mempty
foldMapCat f (C a as) = f a <> foldMapQ (foldMapCat f) as

{-# complete Nil, C #-}
{-# complete E, Cons #-}
{-# complete Nil, Cons :: Cat #-}

instance Default (Cat a) where
  def = E

instance Relative a => Semigroup (Cat a) where
  E <> xs = xs
  xs <> E = xs
  C x xs <> ys = link x xs ys

instance Relative a => Monoid (Cat a) where
  mempty = E

instance Relative a => IsList (Cat a) where
  type Item (Cat a) = a
  fromList = foldr cons nil
  fromListN _ = foldr cons nil
  toList = foldMapCat pure

link :: Relative a => a -> Q (Cat a) -> Cat a -> Cat a
link x xs ys = C x (snoc xs ys)

-- O(1+e) where e is the number of empty catenable lists in the Q
linkAll :: Relative a => Q (Cat a) -> Cat a
linkAll q = case uncons q of
  c@(C a t) :&: q' -> case uncons q' of
    Empty -> c
    _ -> link a t (linkAll q')
  E :&: q' -> linkAll q' -- recursive case in case of empty queues, unused
  Empty -> E

instance Nil Cat where
  nil = E

instance Uncons Cat where
  uncons E = Empty
  uncons (C a q) = a :&: linkAll q

instance Cons Cat where
  cons a E  = C a nil
  cons a ys = link a nil ys

instance Singleton Cat where
  singleton a = C a nil

instance Snoc Cat where
  snoc xs a = xs <> singleton a
