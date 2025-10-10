||| Specialised set of `Fin`s.
||| Isomorphic to a vector of appropriate size of booleans.
|||
||| This should be a replacement for `SortedSet (Fin n)` working better at least in elaborator scripts.
||| This can be implemented as simple `Integer` setting and clearing bits, but this seems to work worse in elaborator scripts.
module Data.Fin.Set

import Data.Bits
import Data.Fin.Map
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect

%default total

export
data FinSet : Nat -> Type where
  MkFS : Integer -> FinSet n

mask : (n : Nat) -> Integer
mask n = (1 `shiftL` n) - 1

%inline
unFS : FinSet n -> Integer
unFS (MkFS bs) = bs

%inline
wrap : (Integer -> Integer) -> FinSet n -> FinSet n
wrap f $ MkFS x = MkFS $ f x

%inline
wrap2 : (Integer -> Integer -> Integer) -> FinSet n -> FinSet n -> FinSet n
wrap2 f (MkFS l) (MkFS r) = MkFS $ f l r

export %inline
empty : FinSet n
empty = MkFS zeroBits

export %inline
full : FinSet n
full = MkFS oneBits

export %inline
complement : FinSet n -> FinSet n
complement = wrap $ Bits.complement

export %inline
insert : Fin n -> FinSet n -> FinSet n
insert i = wrap (`setBit` finToNat i)

export %inline
insert' : FinSet n -> Fin n -> FinSet n
insert' = flip insert

export %inline
delete : Fin n -> FinSet n -> FinSet n
delete i = wrap (`clearBit` finToNat i)

export %inline
delete' : FinSet n -> Fin n -> FinSet n
delete' = flip delete

export %inline
contains : Fin n -> FinSet n -> Bool
contains i = (`testBit` finToNat i) . unFS

export %inline
contains' : FinSet n -> Fin n -> Bool
contains' = flip contains

export %inline
fromFoldable : Foldable f => f (Fin n) -> FinSet n
fromFoldable = foldl insert' $ empty {n}

export %inline
fromList : List (Fin n) -> FinSet n
fromList = fromFoldable

export %inline
toList : {n : _} -> FinSet n -> List (Fin n)
toList {n=Z}   = const []
toList {n=S n} = go n last [] . unFS where
  go : Nat -> Fin (S n) -> List (Fin $ S n) -> Integer -> List (Fin $ S n)
  go _ FZ        acc i = if testBit i 0 then FZ :: acc else acc
  go n k@(FS k') acc i = let next = if testBit i n then k :: acc else acc in go (n `minus` 1) (assert_smaller k $ believe_me k') next i

export
traverse_ : Monad m => {n : _} -> (Fin n -> m b) -> FinSet n -> m ()
traverse_ {n=Z}       _ = const $ pure ()
traverse_ {n=n@(S _)} f = go FZ . (mask n .&.) . unFS where
  go : Fin n -> Integer -> m ()
  go _   0 = pure ()
  go idx i = do
    let %inline next : m ()
        next = go (believe_me $ FS idx) (assert_smaller i $ i `shiftR` 1)
    if testBit i 0 then ignore (f idx) >> next else next

public export %inline
for_ : Monad m => {n : _} -> FinSet n -> (Fin n -> m b) -> m ()
for_ = flip traverse_

export
foldl : {n : _} -> (a -> Fin n -> a) -> a -> FinSet n -> a
foldl {n=Z}       _ ini = const ini
foldl {n=n@(S _)} f ini = go FZ ini . unFS where
  go : Fin n -> a -> Integer -> a
  go _   curr 0 = curr
  go idx curr i = let next = if testBit i 0 then f curr idx else curr in go (believe_me $ FS idx) next (assert_smaller i $ i `shiftR` 1)

public export
foldMap : Monoid m => {n : _} -> (Fin n -> m) -> FinSet n -> m
foldMap f = foldl (\c => (c <+>) . f) neutral

public export %inline
(.asList) : {n : _} -> FinSet n -> List (Fin n)
(.asList) = toList

public export %inline
size : {n : _} -> FinSet n -> Nat
size = length . toList {n} -- this implementation is to make `asVect` work seamlessly

public export %inline
(.size) : {n : _} -> FinSet n -> Nat
(.size) = size {n}

public export %inline
(.asVect) : {n : _} -> (fs : FinSet n) -> Vect fs.size (Fin n)
(.asVect) fs = fromList $ toList fs

export %inline
union : FinSet n -> FinSet n -> FinSet n
union = wrap2 (.|.)

export %inline
difference : FinSet n -> FinSet n -> FinSet n
difference (MkFS l) (MkFS r) = MkFS $ l .&. complement r

export %inline
symDifference : FinSet n -> FinSet n -> FinSet n
symDifference = wrap2 xor

export %inline
intersection : FinSet n -> FinSet n -> FinSet n
intersection = wrap2 (.&.)

export %inline
leftMost : {n : _} -> FinSet n -> Maybe $ Fin n
leftMost = go n . unFS where
  go : (n : Nat) -> Integer -> Maybe $ Fin n
  go _     0 = Nothing
  go 0     _ = Nothing
  go (S n) x = if testBit x 0 then Just FZ else FS <$> go n (x `shiftR` 1)

export %inline
rightMost : {n : _} -> FinSet n -> Maybe $ Fin n
rightMost = go n . unFS where
  go : (n : Nat) -> Integer -> Maybe $ Fin n
  go _     0 = Nothing
  go 0     _ = Nothing
  go (S n) x = if testBit x n then Just last else weaken <$> go n x

export
{n : _} -> Show (FinSet n) where
  showPrec d s = showCon d "fromList" $ showArg $ toList s

export
{n : _} -> Eq (FinSet n) where
  (==) = (==) `on` (mask n .&.) . unFS

export
{n : _} -> Ord (FinSet n) where
  compare = comparing $ (mask n .&.) . unFS

export
Semigroup (FinSet n) where
  (<+>) = union {n}

export
Monoid (FinSet n) where
  neutral = empty {n}

export
{n : _} -> Interpolation (Fin n) => Interpolation (FinSet n) where
  interpolate = ("{" ++) . (++ "}") . joinBy ", " . map interpolate . Fin.Set.toList {n}

export
null : {n : _} -> FinSet n -> Bool
null (MkFS x) = mask n .&. x == 0

namespace SortedMap

  export
  keySet : {n : _} -> SortedMap (Fin n) v -> FinSet n
  keySet = fromFoldable . map fst . SortedMap.toList

  export
  keySetSize : (m : SortedMap (Fin n) v) -> (keySet m).size = length (SortedMap.toList m)
  keySetSize _ = believe_me $ Refl {x=Z}

namespace FinMap

  export
  keySet : {n : _} -> FinMap n v -> FinSet n
  keySet = fromFoldable . map fst . kvList

  export
  keySetSize : (m : FinMap n v) -> (keySet m).size = length (kvList m)
  keySetSize _ = believe_me $ Refl {x=Z}

namespace SortedSet

  export %inline
  toSortedSet : {n : _} -> FinSet n -> SortedSet (Fin n)
  toSortedSet = fromList . toList

export
singleton : Fin n -> FinSet n
singleton = MkFS . setBit zeroBits . finToNat

export
fit : {n : _} -> FinSet n -> FinSet m
fit (MkFS x) = MkFS $ mask n .&. x

export %inline
weakenToSuper : {i : _} -> FinSet (finToNat i) -> FinSet n
weakenToSuper = fit
