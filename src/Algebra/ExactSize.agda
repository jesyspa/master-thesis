module Algebra.ExactSize where

open import ThesisPrelude
open import Algebra.Function

HasSize : ∀{l} (A : Set l) (n : Nat) → Set l
HasSize A n = Fin n ↔ A

size1-lem : ∀{l} (A : Set l) → (a : A) → (∀ a′ → a′ ≡ a) → HasSize A 1
size1-lem A a p = const a , const zero , (λ { zero → refl ; (suc ()) }) , p

size0-lem : ∀{l} (A : Set l) → (∀(a : A) → ⊥) → HasSize A 0
size0-lem A p = (λ ()) , (λ x → ⊥-elim (p x)) , (λ ()) , λ a → ⊥-elim (p a)
  
get-unique : ∀{l} {A : Set l} → HasSize A 1 → A
get-unique (f , _) = f zero

fin1-unique : (x y : Fin 1) → x ≡ y
fin1-unique zero zero = refl
fin1-unique zero (suc ())
fin1-unique (suc ()) _

is-unique : ∀{l} {A : Set l} → HasSize A 1 → (x y : A) → x ≡ y
is-unique (f , fi , r , s) x y = s x ⟨≡⟩ cong f (fin1-unique (fi x) (fi y)) ⟨≡⟩ʳ s y

is-empty : ∀{l} {A : Set l} → HasSize A 0 → A → ⊥ 
is-empty (f , fi , _) a with fi a
... | ()
