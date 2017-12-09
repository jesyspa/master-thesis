module Functor where

open import MiniPrelude
open import Category

record Functor {Ob : Set} {Hom : Ob → Ob → Set} {{cat : SmallCategory Ob Hom}} (M : Ob → Set) : Set where
  field
    map : ∀{i j} → Hom i j → M i → M j
    map-id : ∀{i} → (a : M i) → a ≡ map (id i) a
    map-comp : ∀{i j k} → (a : M i)
                → (q : Hom j k) → (p : Hom i j)
                → map (q ∘ p) a ≡ map q (map p a) 
