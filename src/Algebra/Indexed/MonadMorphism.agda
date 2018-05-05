open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

open import Algebra.Function

record IxMonadMorphism {l} : Set (lsuc l ⊔ lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    StateM : S₁ → S₂ → Set (l ⊔ l₁ ⊔ l₂)
    -- This is kind of terrible.
    TermM  : ∀{A A′ s s′} → (∀{t t′} → StateM t t′ → A t ↔ A′ t′) → StateM s s′ → M₁ A s → M₂ A′ s′

