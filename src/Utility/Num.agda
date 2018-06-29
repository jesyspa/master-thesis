module Utility.Num where

open import ThesisPrelude
open import Algebra.Function

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 *N pow2 n

postulate
  -- Obviously true, too much hassle to prove now.
  pow2-nz : ∀ n → ¬ (pow2 n ≡ zero)

suc-Inj : Injective Nat.suc
suc-Inj {zero} {.zero} refl = refl
suc-Inj {suc x} {.(suc x)} refl = refl

add-Inj : (n : Nat) → Injective (_+_ n)
add-Inj n eq = by eq

add-assoc : (i j k : Nat) → i + j + k ≡ i + (j + k)
add-assoc i j k = auto

≤N-get-diff : ∀{n k : Nat} → n ≤ k → Nat
≤N-get-diff (diff i eq) = i

≤N-get-eq : ∀{n k : Nat} → (le : n ≤ k) → k ≡ n + ≤N-get-diff le
≤N-get-eq (diff i refl) = auto

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

