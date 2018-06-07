open import ThesisPrelude
module Algebra.Indexed.MonadMorphism {l₁ l₂ l′}{S₁ : Set l₁}{S₂ : Set l₂}
                                     (M₁ : (S₁ → Set l′) → S₁ → Set l′)
                                     (M₂ : (S₂ → Set l′) → S₂ → Set l′) where

open import Algebra.Indexed.Monad
open import Algebra.Function
open import Algebra.Relation

record IxMonadMorphism (f : S₁ → S₂) : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxMM  : ∀{A s} → M₁ (A ∘′ f) s → M₂ A (f s)

record IxStrongMonadMorphism (f : S₁ → S₂) : Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxSMM  : ∀{A₁ A₂ s} → (∀{s′} → A₁ s′ → A₂ (f s′)) → M₁ A₁ s → M₂ A₂ (f s)

module _ (f : S₁ → S₂) where
  open IxStrongMonadMorphism
  open IxMonadMorphism
  from-strong : IxStrongMonadMorphism f → IxMonadMorphism f
  RunIxMM (from-strong mn) m = RunIxSMM mn id m

record IxMonadComorphism (f : S₂ → S₁): Set (lsuc l₁ ⊔ lsuc l₂ ⊔ lsuc l′) where
  field
    RunIxMCM  : ∀{A s} → M₁ A (f s) → M₂ (A ∘′ f) s
