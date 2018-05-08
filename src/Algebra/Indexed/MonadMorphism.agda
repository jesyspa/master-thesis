open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

open import Algebra.Function

record IxMonadMorphism : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    StateM : S₁ → S₂
    -- This is kind of terrible.
    TermM  : ∀{A s} → M₁ (A ∘′ StateM) s → M₂ A (StateM s)

