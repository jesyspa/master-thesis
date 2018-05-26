open import ThesisPrelude
module Algebra.Indexed.MonadRelMorphism {S₁ S₂ : Set}
                                        (M₁ : (S₁ → Set) → S₁ → Set)
                                        (M₂ : (S₂ → Set) → S₂ → Set) where

open import Algebra.Function
open import Algebra.Relation

record IxMonadRelMorphism (R : Relation S₁ S₂) : Set₁ where
  constructor ix-rel-mmorphism
  field
    TermRM  : ∀{A A′ s s′} → R s s′ → (∀{t t′} → R t t′ → A t → A′ t′) → M₁ A s → M₂ A′ s′
