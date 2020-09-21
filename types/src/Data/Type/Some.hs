{-# Language PolyKinds #-}
{-# Language TypeApplications #-}
module Data.Type.Some 
  ( Some(Some)
  , singSome
  , someSing
  ) where

import Data.Type.Internal
import Data.Some

someSing :: Some (Sing @a) -> a
someSing (Some (Sing a)) = a
{-# inline someSing #-}

singSome :: a -> Some (Sing @a)
singSome a = Some (SING a)
{-# inline singSome #-}
