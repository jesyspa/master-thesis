module Utility.Num where

open import ThesisPrelude
open import Algebra.Function

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 *N pow2 n

postulate
  -- Obviously true, too much hassle to prove now.
  pow2-nz : ∀ n → ¬ (pow2 n ≡ zero)
