||| Conversions of `Fin`s to `Fin`s
module Data.Fin.ToFin

import public Data.Fin

%default total

public export
tryToFit : {to : _} -> Fin from -> Maybe $ Fin to
tryToFit {to=0}   _      = Nothing
tryToFit {to=S _} FZ     = Just FZ
tryToFit {to=S _} (FS x) = FS <$> tryToFit x

-- weakens the left part, shifts the right one
public export
weakenOrShift : (left, mid : _) -> Fin (left + right) -> Fin (left + mid + right)
weakenOrShift Z     mid x      = shift mid x
weakenOrShift (S n) mid FZ     = FZ
weakenOrShift (S n) mid (FS x) = FS $ weakenOrShift n mid x

public export
weakenToSuper : {i : Fin n} -> Fin (finToNat i) -> Fin n
weakenToSuper {i = FS _} FZ     = FZ
weakenToSuper {i = FS _} (FS x) = FS $ weakenToSuper x

export
weakenToSuper_correct : {i : Fin n} -> (x : Fin $ finToNat i) -> finToNat (weakenToSuper {i} x) = finToNat x
weakenToSuper_correct {i = FS _} FZ     = Refl
weakenToSuper_correct {i = FS _} (FS x) = cong S $ weakenToSuper_correct x

export
weakenOrShiftWithNoShiftIsWeakenN : (left, mid : _) -> (x' : Fin $ left + 0) -> (x : Fin left) -> x' ~~~ x =>
                                    weakenOrShift left mid {right=0} x' ~~~ weakenN mid x
weakenOrShiftWithNoShiftIsWeakenN _        _   FZ      FZ             = FZ
weakenOrShiftWithNoShiftIsWeakenN (S left) mid (FS x') (FS x) @{FS _} = FS $ weakenOrShiftWithNoShiftIsWeakenN left mid x' x
