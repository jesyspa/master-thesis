module Algebra.Equality where

open import ThesisPrelude

yes-refl : ∀{l} {A : Set l} {{_ : Eq A}} (a : A) → isYes (a == a) ≡ true
yes-refl a with a == a
... | yes eq = refl
... | no neq = ⊥-elim (neq refl)

yes-refl′ : ∀{l} {A : Set l} {{_ : Eq A}} (a : A) → (a == a) ≡ yes refl 
yes-refl′ a with a == a
... | yes refl = refl
... | no neq   = ⊥-elim (neq refl)

no-neq : ∀{l} {A : Set l} {{_ : Eq A}} (a a′ : A) → ¬ (a ≡ a′) → isYes (a == a′) ≡ false
no-neq a a′ p with a == a′
... | yes eq = ⊥-elim (p eq)
... | no neq = refl

neq-is-no : ∀{l} {A : Set l} {{_ : Eq A}} {a a′ : A} → ¬ (a ≡ a′) → IsTrue (isNo (a == a′))
neq-is-no {a = a} {a′} neq with a == a′
... | yes refl = ⊥-elim (neq refl)
... | no _ = true

flip-transport : ∀{l l′} {A : Set l} (B : A → Set l′) {a a′}
               → (p : a ≡ a′) → (b : B a) (b′ : B a′)
               → b ≡ transport B (sym p) b′
               → transport B p b ≡ b′
flip-transport B refl .b′ b′ refl = refl

split-pair-eq : ∀{l}{A B : Set l}{a₁ a₂ : A}{b₁ b₂ : B}
              → (a₁ , b₁) ≡ (a₂ , b₂)
              → (a₁ ≡ a₂) × (b₁ ≡ b₂)
split-pair-eq {a₁ = a₁} {.a₁} {b₁} {.b₁} refl = refl , refl
