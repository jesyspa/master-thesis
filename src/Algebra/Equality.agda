module Algebra.Equality where

open import ThesisPrelude

yes-refl : ∀{l} {A : Set l} {{_ : Eq A}} (a : A) → isYes (a == a) ≡ true
yes-refl a with a == a
... | yes eq = refl
... | no neq = ⊥-elim (neq refl)
