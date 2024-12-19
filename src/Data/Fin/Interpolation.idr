module Data.Fin.Interpolation

import public Data.Fin

%default total

export %defaulthint
FromShow : Interpolation (Fin n)
FromShow = I where [I] Interpolation (Fin n) where interpolate = show
