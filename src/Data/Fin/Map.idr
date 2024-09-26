||| Specialised map from `Fin`s to any type.
||| Isomorphic to a vector of appropriate size of maybe's of appropriate type.
|||
||| This should be a replacement for `SortedMap (Fin n) v` working better at least in elaborator scripts.
module Data.Fin.Map

import Data.List
import Data.SortedMap
import Data.String
import Data.Vect

%default total

export
data FinMap : Nat -> Type -> Type where
  MkFM : Vect n (Maybe v) -> FinMap n v

%inline
unFM : FinMap n v -> Vect n $ Maybe v
unFM (MkFM bs) = bs

export %inline
empty : {n : _} -> FinMap n v
empty = MkFM $ replicate _ Nothing

export %inline
lookup : Fin n -> FinMap n v -> Maybe v
lookup i = index i . unFM

export %inline
lookup' : FinMap n v -> Fin n -> Maybe v
lookup' = flip lookup

export %inline
insert : Fin n -> v -> FinMap n v -> FinMap n v
insert i x = MkFM . replaceAt i (Just x) . unFM

export
insertWith : (v -> v -> v) -> Fin n -> v -> FinMap n v -> FinMap n v
insertWith f i x = MkFM . updateAt i (Just . maybe x (f x)) . unFM

public export %inline
insert' : FinMap n v -> (Fin n, v) -> FinMap n v
insert' = flip $ uncurry insert

export %inline
singleton : {n : _} -> Fin n -> v -> FinMap n v
singleton i x = insert i x empty

export %inline
insertFrom : Foldable f => f (Fin n, v) -> FinMap n v -> FinMap n v
insertFrom = flip $ foldl insert'

export %inline
insertFrom' : Foldable f => FinMap n v -> f (Fin n, v) -> FinMap n v
insertFrom' = flip insertFrom

export %inline
insertFromWith : Foldable f => (v -> v -> v) -> f (Fin n, v) -> FinMap n v -> FinMap n v
insertFromWith = flip . foldl . flip . uncurry . insertWith

export %inline
delete : Fin n -> FinMap n v -> FinMap n v
delete i = MkFM . replaceAt i Nothing . unFM

export %inline
delete' : FinMap n v -> Fin n -> FinMap n v
delete' = flip delete

export %inline
update : (Maybe v -> Maybe v) -> Fin n -> FinMap n v -> FinMap n v
update f i = MkFM . updateAt i f . unFM

public export %inline
update' : FinMap n v -> (Maybe v -> Maybe v) -> Fin n -> FinMap n v
update' m f x = update f x m

export %inline
updateExisting : (v -> v) -> Fin n -> FinMap n v -> FinMap n v
updateExisting f i = MkFM . updateAt i (map f) . unFM

public export %inline
updateExisting' : FinMap n v -> (v -> v) -> Fin n -> FinMap n v
updateExisting' m f x = updateExisting f x m

export %inline
fromFoldable : Foldable f => {n : _} -> f (Fin n, v) -> FinMap n v
fromFoldable = insertFrom' empty

export %inline
fromFoldableWith : Foldable f => {n : _} -> (v -> v -> v) -> f (Fin n, v) -> FinMap n v
fromFoldableWith f = flip (insertFromWith f) empty

export %inline
fromList : {n : _} -> List (Fin n, v) -> FinMap n v
fromList = insertFrom' empty

export %inline
fromListWith : {n : _} -> (v -> v -> v) -> List (Fin n, v) -> FinMap n v
fromListWith f = flip (insertFromWith f) empty

export -- I do this here just not to depend on libraries like `collection-utils`
iList : Vect n a -> List (Fin n, a)
iList [] = []
iList (x::xs) = (FZ, x) :: (mapFst FS <$> iList xs)

export %inline
kvList : FinMap n v -> List (Fin n, v)
kvList = mapMaybe (\(i, mv) => (i,) <$> mv) . iList . unFM

public export %inline
(.asKVList) : FinMap n v -> List (Fin n, v)
(.asKVList) = kvList

export
keys : FinMap n v -> List $ Fin n
keys = map fst . kvList

export
values : FinMap n v -> List v
values = map snd . kvList

export
Functor (FinMap n) where
  map f = MkFM . map @{Compose} f . unFM

export
Foldable (FinMap n) where
  foldr f z = foldr f z . values
  foldl f z = foldl f z . values
  null      = all isNothing . unFM
  foldMap f = foldMap f . values

export
Traversable (FinMap n) where
  traverse f = map MkFM . traverse @{Compose} f . unFM

export
Zippable (FinMap n) where
  zipWith f mx my = MkFM $ zipWith (\x, y => f <$> x <*> y) (unFM mx) (unFM my)
  zipWith3 f mx my mz = MkFM $ zipWith3 (\x, y, z => f <$> x <*> y <*> z) (unFM mx) (unFM my) (unFM mz)
  unzipWith f m = let m' = map f m in (map fst m', map snd m')
  unzipWith3 f m = let m' = map f m in (map fst m', map (fst . snd) m', map (snd . snd) m')

||| Merge two maps, when encountering duplicate keys, uses a function to combine the values.
export
mergeWith : (v -> v -> v) -> FinMap n v -> FinMap n v -> FinMap n v
mergeWith f = MkFM .: zipWith fm `on` unFM where
  fm : Maybe v -> Maybe v -> Maybe v
  fm Nothing  Nothing  = Nothing
  fm (Just x) Nothing  = Just x
  fm Nothing  (Just y) = Just y
  fm (Just x) (Just y) = Just $ f x y

public export %inline
merge : Semigroup v => FinMap n v -> FinMap n v -> FinMap n v
merge = mergeWith (<+>)

public export %inline
mergeLeft : FinMap n v -> FinMap n v -> FinMap n v
mergeLeft = mergeWith const

export %inline
leftMost : FinMap n v -> Maybe (Fin n, v)
leftMost = head' . kvList

export %inline
rightMost : FinMap n v -> Maybe (Fin n, v)
rightMost = last' . kvList

export
Interpolation v => Interpolation (Fin n) => Interpolation (FinMap n v) where
  interpolate = ("{" ++) . (++ "}") . joinBy ", " . map (\(i, v) => "\{i} -> \{v}") . kvList

export
Eq v => Eq (FinMap n v) where
  (==) = (==) `on` unFM

export
Semigroup v => Semigroup (FinMap n v) where
  (<+>) = merge

export
{n : _} -> Semigroup v => Monoid (FinMap n v) where
  neutral = empty

public export %inline
size : FinMap n v -> Nat
size = length . kvList -- this implementation is to make `asVect` work seamlessly

public export %inline
(.size) : FinMap n v -> Nat
(.size) = size

public export %inline
(.asKVVect) : (fs : FinMap n v) -> Vect fs.size (Fin n, v)
(.asKVVect) fs = fromList $ kvList fs

export
fromSortedMap : {n : _} -> SortedMap (Fin n) v -> FinMap n v
fromSortedMap = fromList . SortedMap.toList
-- we can employ the fact that the returned list must be sorted to make this faster

export
weakenToSuper : {n : _} -> {i : Fin n} -> FinMap (finToNat i) v -> FinMap n v
weakenToSuper = MkFM . go . unFM where
  go : {n : _} -> {i : Fin n} -> Vect (finToNat i) (Maybe v) -> Vect n (Maybe v)
  go {i=FZ}   []      = replicate _ Nothing
  go {i=FS i} (x::xs) = x :: go xs
