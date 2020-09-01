{-# Language TypeFamilies #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}

module Data.Type.Tuple
  ( Fst
  , Snd
  ) where

type family Fst (p :: (a,b)) :: a where
  Fst '(a,b) = a

type family Snd (p :: (a,b)) :: b where
  Snd '(a,b) = b
