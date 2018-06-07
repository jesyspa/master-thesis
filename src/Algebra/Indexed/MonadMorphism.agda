open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

open import Algebra.Function
open import Algebra.Relation

record IxMonadMorphism (f : S₁ → S₂) : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxMM  : ∀{A s} → M₁ (A ∘′ f) s → M₂ A (f s)

record IxWeakMonadMorphism (f : S₁ → S₂) : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxWMM  : ∀{A₁ A₂ s} → (∀{s′} → A₁ s′ → A₂ (f s′)) → M₁ A₁ s → M₂ A₂ (f s)

record IxMonadComorphism (f : S₂ → S₁): Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxMCM  : ∀{A s} → M₁ A (f s) → M₂ (A ∘′ f) s
