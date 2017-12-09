module IndexedMonoid where

open import MiniPrelude
open import Monoid
open import Functor
open import Category

record IndexedMonoid {Ob : Set} {Hom : Ob → Ob → Set}
                     {{cat : SmallCategory Ob Hom}}
                     (M : Ob → Set) {{Functor M}} : Set where
  infixr 6 _^_
  infixr 6 _⊕_
  field

    _^_ : Nat → Nat → Nat 
    ixop-assoc : ∀{i j k} → i ^ (j ^ k) ≡ (i ^ j) ^ k

    unit : ∀{n} → M n
    _⊕_ : ∀{i j} → M i → M j → M (i ^ j)
    action-assoc : ∀{i j k} → (a : M i) → (b : M j) → (c : M k)
                 → transport M ixop-assoc (a ⊕ (b ⊕ c)) ≡ (a ⊕ b) ⊕ c 
    
