open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

record IxMonadMorphism : Set (l₁ ⊔ l₂ ⊔ lsuc l′) where
  field
    StateM : S₂ → S₁
    TermM  : ∀{A s} → M₁ A (StateM s) → M₂ (A ∘′ StateM) s

