<!-- idris
module README

import Data.Fin.Minus
import Data.Fin.Lists
import Data.Fin.ToFin
-->

# Fin Lizzie

Additional utilities for `Data.Fin` for Idris 2

## Type-safe injective minus

Three is a `minus` function in `prelude` which subtracts a `Nat` from `Nat`.
But it allows to subtract greater number from the smaller one,
which is inconvenient when you try to track different kind of length and sizes in types
and apply such operations to those indices.
That's why this library adds a `-` operation which allows to subtract only appropriate numbers
and is indeed inverse to the addition operation.

```idris
FifteenMinusSix : Nat
FifteenMinusSix = 15 - 6

fifteenMinusSixIsCorrect : FifteenMinusSix = 9
fifteenMinusSixIsCorrect = Refl
```

This is done by requiring the second argument to be `Fin (S n)` when subtracting from the natural `n`.
So, you cannot do the following:

```idris
failing "Can't find an implementation for So"
  FiveMinusSeven : Nat
  FiveMinusSeven = 5 - 7
```

## Ranges of `Fin`s

Idris supports nice Haskell-style syntax for ranged lists.
But you cannot do this for ranges of `Fin`s using the standard library.
With this library you can do

```idris
listOfFins : List $ Fin 10
listOfFins = [2 .. 8]
```

## Conversions

There are some convenient conversions that I'm afraid to propose to add to the standard library.
For example, sometimes you have a `Fin` indexed by another `Fin`
(for example, when you have a triangle matrix stored in a dependent `Vect`).
In this situation you will need a conversion from `Fin (finToNat i)` to `Fin n` when `i` is of type `Fin n`,
i.e. generalising the `Fin`:

```idris
OuterLength : Nat
LocalLength : Fin OuterLength
localIndex : Fin $ finToNat LocalLength

covertedIndex : Fin OuterLength
covertedIndex = weakenToSuper localIndex
```
