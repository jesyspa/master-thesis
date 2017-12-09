module NatSucMax where

open import MiniPrelude
open import Semigroup

max : Nat → Nat → Nat
max zero j = j
max (suc i) zero = suc i
max (suc i) (suc j) = suc (max i j)

max-commute : ∀ i j → max i j ≡ max j i
max-commute zero zero = refl
max-commute zero (suc j) = refl
max-commute (suc i) zero = refl
max-commute (suc i) (suc j) = cong suc (max-commute i j)

max-assoc : ∀ i j k → max i (max j k) ≡ max (max i j) k
max-assoc zero j k = refl
max-assoc (suc i) zero k = refl
max-assoc (suc i) (suc j) zero = refl
max-assoc (suc i) (suc j) (suc k) = cong suc (max-assoc i j k)

suc-max : Nat → Nat → Nat
suc-max i j = suc (max i j)

suc-max-commute : ∀ i j → suc-max i j ≡ suc-max j i
suc-max-commute i j = cong suc (max-commute i j) 

-- You know, I guess this might not be true.
suc-max-assoc : ∀ i j k → suc-max i (suc-max j k) ≡ suc-max (suc-max i j) k
suc-max-assoc i j k = cong suc {!!}

{-
instance
  SemigroupNatSucMax : Semigroup Nat
  _^_ {{SemigroupNatSucMax}} = suc-max
  semigroup-assoc {{SemigroupNatSucMax}} i j k = {!!}

-}
