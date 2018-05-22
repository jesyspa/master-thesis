open import ThesisPrelude
module Algebra.Indexed.MonadRelMorphism {S₁ S₂ : Set}
                                        (M₁ : (S₁ → Set) → S₁ → Set)
                                        (M₂ : (S₂ → Set) → S₂ → Set) where

open import Algebra.Function
open import Algebra.Relation

record IxMonadRelMorphism : Set₁ where
  field
    StateRM : Relation S₁ S₂
    TermRM  : ∀{A A′ s s′} → StateRM s s′ → (∀{t t′} → StateRM t t′ → A t → A′ t′) → M₁ A s → M₂ A′ s′
