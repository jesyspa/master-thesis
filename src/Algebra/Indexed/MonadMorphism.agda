open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

open import Algebra.Function
open import Algebra.Relation

record IxMonadMorphism : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    StateM : S₁ → S₂
    TermM  : ∀{A s} → M₁ (A ∘′ StateM) s → M₂ A (StateM s)

record IxMonadComorphism : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    StateCM : S₂ → S₁
    TermCM  : ∀{A s} → M₁ A (StateCM s) → M₂ (A ∘′ StateCM) s
