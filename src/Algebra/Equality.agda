module Algebra.Equality where

open import ThesisPrelude

yes-refl : ∀{l} {A : Set l} {{_ : Eq A}} (a : A) → isYes (a == a) ≡ true
yes-refl a with a == a
... | yes eq = refl
... | no neq = ⊥-elim (neq refl)

flip-transport : ∀{l l′} {A : Set l} (B : A → Set l′) {a a′}
               → (p : a ≡ a′) → (b : B a) (b′ : B a′)
               → b ≡ transport B (sym p) b′
               → transport B p b ≡ b′
flip-transport B refl .b′ b′ refl = refl
