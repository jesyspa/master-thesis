module Utility.Num where

open import ThesisPrelude
open import Algebra.Function

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n +N pow2 n

pow2-Inj : Injective pow2
pow2-Inj {x} {y} p = {!!}
