module Utility.Num where

open import ThesisPrelude

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n +N pow2 n
