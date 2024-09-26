||| Specialised set of `Fin`s.
||| Isomorphic to a vector of appropriate size of booleans.
|||
||| This should be a replacement for `SortedSet (Fin n)` working better at least in elaborator scripts.
||| This can be implemented as simple `Integer` setting and clearing bits, but this seems to work worse in elaborator scripts.
module Data.Fin.Set

import Data.List
import Data.Fin.Map
import Data.SortedMap
import Data.String
import Data.Vect

%default total

export
data FinSet : Nat -> Type where
  MkFS : Vect n Bool -> FinSet n

%inline
unFS : FinSet n -> Vect n Bool
unFS (MkFS bs) = bs

export %inline
empty : {n : _} -> FinSet n
empty = MkFS $ replicate _ False

export %inline
full : {n : _} -> FinSet n
full = MkFS $ replicate _ True

export %inline
complement : FinSet n -> FinSet n
complement = MkFS . map not . unFS

export %inline
insert : Fin n -> FinSet n -> FinSet n
insert i = MkFS . replaceAt i True . unFS

export %inline
insert' : FinSet n -> Fin n -> FinSet n
insert' = flip insert

export %inline
delete : Fin n -> FinSet n -> FinSet n
delete i = MkFS . replaceAt i False . unFS

export %inline
delete' : FinSet n -> Fin n -> FinSet n
delete' = flip delete

export %inline
contains : Fin n -> FinSet n -> Bool
contains i = index i . unFS

export %inline
contains' : FinSet n -> Fin n -> Bool
contains' = flip contains

-- much more effective implementation exists if we know that given foldable is sorted
export %inline
fromFoldable : Foldable f => {n : _} -> f (Fin n) -> FinSet n
fromFoldable = foldl insert' empty

export %inline
fromList : {n : _} -> List (Fin n) -> FinSet n
fromList = fromFoldable

export %inline
toList : FinSet n -> List (Fin n)
toList = map fst . filter snd . iList . unFS

public export %inline
(.asList) : FinSet n -> List (Fin n)
(.asList) = toList

public export %inline
size : FinSet n -> Nat
size = length . toList -- this implementation is to make `asVect` work seamlessly
--size = foldl (\n, b => if b then S n else n) 0 . unFS

public export %inline
(.size) : FinSet n -> Nat
(.size) = size

public export %inline
(.asVect) : (fs : FinSet n) -> Vect fs.size (Fin n)
(.asVect) fs = fromList $ toList fs

export %inline
union : FinSet n -> FinSet n -> FinSet n
union = MkFS .: zipWith (\x, y => x || y) `on` unFS

export %inline
difference : FinSet n -> FinSet n -> FinSet n
difference = MkFS .: zipWith (\l, r => l && not r) `on` unFS

export %inline
symDifference : FinSet n -> FinSet n -> FinSet n
symDifference = MkFS .: zipWith (\l, r => l /= r) `on` unFS

export %inline
insersection : FinSet n -> FinSet n -> FinSet n
insersection = MkFS .: zipWith (\x, y => x && y) `on` unFS

export %inline
leftMost : FinSet n -> Maybe $ Fin n
leftMost = findIndex id . unFS

export %inline
rightMost : FinSet n -> Maybe $ Fin n
rightMost = last' . findIndices id . unFS

export
Semigroup (FinSet n) where
  (<+>) = union

export
{n : _} -> Monoid (FinSet n) where
  neutral = empty

export
Interpolation (Fin n) => Interpolation (FinSet n) where
  interpolate = ("{" ++) . (++ "}") . joinBy ", " . map interpolate . Fin.Set.toList

export
null : FinSet n -> Bool
null = all not . unFS

namespace SortedMap

  export
  keySet : {n : _} -> SortedMap (Fin n) v -> FinSet n
  keySet = fromFoldable . map fst . SortedMap.toList
  -- we can employ the fact that given list is sorted

  export
  keySetSize : (m : SortedMap (Fin n) v) -> (keySet m).size = length (SortedMap.toList m)
  keySetSize _ = believe_me $ Refl {x=Z}

namespace FinMap

  export
  keySet : {n : _} -> FinMap n v -> FinSet n
  keySet = fromFoldable . map fst . kvList
  -- we can employ the fact that given list is sorted

  export
  keySetSize : (m : FinMap n v) -> (keySet m).size = length (kvList m)
  keySetSize _ = believe_me $ Refl {x=Z}

export
singleton : {n : _} -> Fin n -> FinSet n
singleton = MkFS . go where
  go : {n : _} -> Fin n -> Vect n Bool
  go FZ     = True  :: replicate _ False
  go (FS i) = False :: go i

export
weakenToSuper : {n : _} -> {i : Fin n} -> FinSet (finToNat i) -> FinSet n
weakenToSuper = MkFS . go . unFS where
  go : {n : _} -> {i : Fin n} -> Vect (finToNat i) Bool -> Vect n Bool
  go {i=FZ}   []      = replicate _ False
  go {i=FS i} (x::xs) = x :: go xs
