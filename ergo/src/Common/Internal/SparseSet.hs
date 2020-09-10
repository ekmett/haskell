{-# Language BlockArguments #-}
{-# Language DataKinds #-}
{-# Language ImportQualifiedPost #-}
{-# Language OverloadedLists #-}
{-# Language RoleAnnotations #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneKindSignatures #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language ViewPatterns #-}
module Common.Internal.SparseSet
  ( MutableSparseSet(..)
  , new -- O(1)
  , insert -- O(1)
  , delete -- O(1)
  , read -- O(1)
  , write -- O(1)
  , reset -- O(1)
  , unsafeFreezeAndShrink -- O(1)
  , unsafeFreeze -- O(1)
  , unsafeThaw -- O(1)
  , capacity -- O(1)
  , getCount -- O(1)

  , SparseSet(..) 
  , count -- O(1)
  , index -- O(1)
  , union -- O(count a + count b)
  , intersection -- O(min (count a) (count b))
  , complement -- O(universe a)
  , difference -- O(count a)
  , Exts.fromList -- O(count) 
  , toList -- O(length)
  , Universe(..) -- O(1)
  ) where

import Common.Internal.Nat
import Control.Monad
import Control.Monad.Primitive
import Data.Foldable (for_)
import Data.Kind (Type)
import Data.Primitive.ByteArray
import Data.Proxy
import Control.Monad.ST
import GHC.Exts qualified as Exts
import GHC.TypeNats
import Foreign.Storable (sizeOf)
import Prelude hiding (read)

type MutableSparseSet :: Type -> Nat -> Type
type role MutableSparseSet nominal nominal
data MutableSparseSet s i = MutableSparseSet
  {-# unpack #-} !(MutableByteArray s)
  {-# unpack #-} !(MutableByteArray s)

instance Eq (MutableSparseSet d s) where
  MutableSparseSet d _ == MutableSparseSet d' _ = d == d'

type SparseSet :: Nat -> Type
type role SparseSet nominal
data SparseSet i = SparseSet
  {-# unpack #-} !ByteArray
  {-# unpack #-} !ByteArray

wordSize :: Int
wordSize = sizeOf (undefined :: Word)
{-# inline wordSize #-}

-- word 0 = size
slot :: Word -> Int
slot n = fromIntegral n + 1
{-# inline slot #-}

readWord :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> m Word
readWord = readByteArray
{-# inline readWord #-}

writeWord :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> Word -> m ()
writeWord = writeByteArray
{-# inline writeWord #-}

-- used when we have an upper bound on the size of the set we'll ever produce
new'' :: PrimMonad m => Int -> Int -> m (MutableSparseSet (PrimState m) i)
new'' nd ns = stToPrim do
  d <- newByteArray $ (min nd ns + 1) * wordSize
  s <- newByteArray $ ns * wordSize
  MutableSparseSet d s <$ writeWord d 0 0

new' :: PrimMonad m => Int -> m (MutableSparseSet (PrimState m) i)
new' n = new'' n n

-- | /O(1)/
new :: PrimMonad m => N i -> m (MutableSparseSet (PrimState m) i)
new = new' . int

-- | /O(1)/
new_ :: forall i m. (PrimMonad m, KnownNat i) => m (MutableSparseSet (PrimState m) i)
new_ = new' $ fromIntegral $ natVal (Proxy @i)

read' :: Word -> MutableByteArray s -> MutableByteArray s -> Int -> ST s Bool
read' n d s i = do
  e <- readWord s i
  if e <= n then (fromIntegral i == ) <$> readWord d (slot e)
  else pure False

-- | /O(1)/
read :: PrimMonad m => MutableSparseSet (PrimState m) i -> Fin i -> m Bool
read (MutableSparseSet d s) (int -> i) = stToPrim do
  n <- readWord d 0
  read' n d s i

-- | /O(1)/
write :: PrimMonad m => MutableSparseSet (PrimState m) i -> Fin i -> Bool -> m ()
write s i True = insert s i
write s i False = delete s i

-- | /O(1)/
insert :: PrimMonad m => MutableSparseSet (PrimState m) i -> Fin i -> m ()
insert (MutableSparseSet d s) (int -> i) = stToPrim do
  n <- readWord d 0
  b <- read' n d s i
  unless b do
    writeWord s i n
    writeWord d (slot n) (fromIntegral i)
    writeWord d 0 (n+1)

-- | /O(1)/
delete :: PrimMonad m => MutableSparseSet (PrimState m) i -> Fin i -> m ()
delete (MutableSparseSet d s) (int -> i) = stToPrim do
  n <- readWord d 0
  b <- read' n d s i
  when b do
    let n' = n-1
    j <- readWord d $ slot n'
    k <- readWord s i
    writeWord d (slot k) j
    readWord s i >>= writeWord s (fromIntegral j)
    writeWord d 0 n'

-- | /O(1)/
unsafeFreeze :: PrimMonad m => MutableSparseSet (PrimState m) i -> m (SparseSet i)
unsafeFreeze (MutableSparseSet d s) = stToPrim $
  SparseSet <$> unsafeFreezeByteArray d <*> unsafeFreezeByteArray s

-- | /O(1)/
--
-- we could even avoid storing the size in the dense array entirely, using the array size
-- but for that i'd need to store the size at the end, which means casual access in the
-- Mutable case would be slower due to having to look up the array length.
unsafeFreezeAndShrink :: PrimMonad m => MutableSparseSet (PrimState m) i -> m (SparseSet i)
unsafeFreezeAndShrink (MutableSparseSet d s) = stToPrim do
  n <- readWord d 0
  shrinkMutableByteArray d (fromIntegral n * wordSize)
  SparseSet <$> unsafeFreezeByteArray d <*> unsafeFreezeByteArray s

-- | /O(1)/
unsafeThaw :: PrimMonad m => SparseSet i -> m (MutableSparseSet (PrimState m) i)
unsafeThaw (SparseSet d s) = stToPrim do
  MutableSparseSet <$> unsafeThawByteArray d <*> unsafeThawByteArray s

-- | /O(1)/
reset :: PrimMonad m => MutableSparseSet (PrimState m) i -> m ()
reset (MutableSparseSet d _) = writeWord d 0 0

class Universe t where
  -- | /O(1)/
  universe :: t i -> N i 

instance Universe SparseSet where
  universe (SparseSet _ s) = UnsafeN $ sizeofByteArray s `div` wordSize
  
instance Universe (MutableSparseSet s) where
  universe (MutableSparseSet _ s) = UnsafeN $ sizeofMutableByteArray s `div` wordSize

-- | /O(1)/
count :: SparseSet i -> Fin i
count (SparseSet d _) = UnsafeFin $ fromIntegral $ indexWord d 0

-- | /O(1)/
-- in the event we shrank the set (during freezing), this may be less than nominalCapacity
-- any attempt to insert more than this elements will likely segfault. don't.
capacity :: MutableSparseSet s i -> Fin i
capacity (MutableSparseSet d _) = UnsafeFin $ (sizeofMutableByteArray d `div` wordSize) - 1

-- | /O(1)/
getCount :: PrimMonad m => MutableSparseSet (PrimState m) i -> m (Fin i)
getCount (MutableSparseSet d _) = UnsafeFin . fromIntegral <$> readWord d 0

indexWord :: ByteArray -> Int -> Word
indexWord = indexByteArray

index' :: Word -> ByteArray -> ByteArray -> Int -> Bool
index' n d s i = e <= n && fromIntegral i == indexWord d (slot e) where
  e = indexWord s i

-- | /O(1)/
index :: SparseSet i -> Fin i -> Bool
index (SparseSet d s) (int -> i) = index' n d s i where
  n = indexWord d 0

-- | O(size a+size b)
union :: SparseSet i -> SparseSet i -> SparseSet i
union a b = fromListNU (n + m) u $ toList a ++ toList b where 
  n = int (count a)
  m = int (count b)
  u = int (universe a)

-- O(universe)
complement :: SparseSet i -> SparseSet i 
complement a = fromListNU (u-k) u $ filter (not . index a) $ UnsafeFin <$> [0..u-1] where
  k = int (count a)
  u = int (universe a)

-- O(min (size a) (size b))
intersection :: SparseSet i -> SparseSet i -> SparseSet i
intersection a b = fromListNU (min n m) u $ 
  if n <= m
  then filter (index b) (toList a)
  else filter (index a) (toList b)
  where
    n = int (count a)
    m = int (count b)
    u = int (universe a)

-- | O(size a)
difference :: SparseSet i -> SparseSet i -> SparseSet i
difference a b = fromListNU (min i (u-j)) u $ do 
  filter (not . index b) (toList a)
  where i = int (count a)
        j = int (count b)
        u = int (universe a)

-- | /O(count)/
-- sparse sets are == if they contain the same elements, note folding over the sets yields
-- potentially different orders
instance Eq (SparseSet i) where
  SparseSet d _ == SparseSet d' s' = n == n' && go 0 where
    go i = i >= n || index' n' d' s' (fromIntegral $ indexWord d $ slot i) && go (i+1)
    n = indexWord d 0
    n' = indexWord d' 0

instance Show (SparseSet i) where
  showsPrec d = showsPrec d . toList

instance Semigroup (SparseSet i) where
  (<>) = union

instance KnownNat i => Monoid (SparseSet i) where
  mempty = []

fromListNU :: Int -> Int -> [Fin i] -> SparseSet i
fromListNU n u xs = runST do
  ms <- new'' n u
  for_ xs $ insert ms
  unsafeFreezeAndShrink ms

instance KnownNat i => Exts.IsList (SparseSet i) where
  type Item (SparseSet i) = Fin i
  fromListN n xs = fromListNU n (fromIntegral $ natVal $ Proxy @i) xs
  fromList xs = runST do
    ms <- new_
    for_ xs $ insert ms
    unsafeFreezeAndShrink ms
  toList = toList

-- | /O(n)/
toList :: SparseSet i -> [Fin i]
toList (SparseSet d _) = go (indexWord d 0) where
  go i
    | i == 0 = []
    | i' <- i - 1 = UnsafeFin (fromIntegral $ indexWord d $ slot i') : go i'
