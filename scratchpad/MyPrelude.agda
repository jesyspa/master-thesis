module MyPrelude where

open import Prelude.Empty public
open import Prelude.Unit public
open import Prelude.Bool public
open import Prelude.Sum public
open import Prelude.Product public
open import Prelude.Function public
open import Prelude.Equality public
open import Prelude.Ord public
open import Prelude.Nat public
open import Prelude.Fin public
open import Prelude.List public
open import Prelude.Vec public
open import Numeric.Rational public
open import Numeric.Nat.Divide public
open import Numeric.Nat.GCD public
open import Prelude.Semiring public
open import Tactic.Nat public

open Semiring {{...}} public
open Eq {{...}} public
open Ord {{...}} public
open IsGCD {{...}} public

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 *N pow2 n

fins : ∀{n} → List (Fin (suc n))
fins {zero} =  [ zero ]
fins {suc n} =  zero ∷ map suc fins

NonZero-pi : ∀{x} → {p q : NonZero x} → p ≡ q
NonZero-pi {zero} {()} {_}
NonZero-pi {suc x} {tt} {tt} = refl
