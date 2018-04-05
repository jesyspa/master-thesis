module Utility.Num where

open import ThesisPrelude
open import Algebra.Function

suc-Inj : Injective Nat.suc
suc-Inj {zero} {.zero} refl = refl
suc-Inj {suc x} {.(suc x)} refl = refl

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = pow2 n +N pow2 n

{-
zero-not-suc : (n : Nat) → ¬ (zero ≡ Nat.suc n)
zero-not-suc zero ()
zero-not-suc (suc n) ()

notzero-suc : (n : Nat) → ¬ (n ≡ zero) → Σ Nat λ k → n ≡ suc k
notzero-suc zero pf = ⊥-elim (pf refl)
notzero-suc (suc n) pf = n , refl

notzero-pow2 : (n : Nat) → ¬ (pow2 n ≡ zero)
notzero-pow2 zero ()
notzero-pow2 (suc n) eq = {!!}

pow2-Inj : Injective pow2
pow2-Inj {zero} {zero} p = refl
pow2-Inj {zero} {suc y} p with notzero-suc (pow2 y) {!!}
... | k , eq = suc-Inj {!p!}
pow2-Inj {suc x} {zero} p = {!!}
pow2-Inj {suc x} {suc y} p = {!!}
-}

postulate
  pow2-Inj : Injective pow2
