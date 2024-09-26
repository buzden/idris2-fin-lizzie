module Data.Fin.Interpolation

import Data.Fin

%default total

export %defaulthint
FromShow : Interpolation (Fin n)
FromShow = I where [I] Interpolation (Fin n) where interpolate = show
