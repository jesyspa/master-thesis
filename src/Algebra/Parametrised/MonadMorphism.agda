module Algebra.Parametrised.MonadMorphism {l l₁′ l₂′}
                                          {𝑺₁ : Set l₁′}(M₁ : 𝑺₁ → 𝑺₁ → Set l → Set l)
                                          {𝑺₂ : Set l₂′}(M₂ : 𝑺₂ → 𝑺₂ → Set l → Set l) where

open import Algebra.Parametrised.Monad

open import ThesisPrelude

record ParMonadMorphism : Set (lsuc l ⊔ l₁′ ⊔ l₂′) where
  field
    StateM : 𝑺₁ → 𝑺₂
    TermM  : ∀{s₁ s₂ A} → M₁ s₁ s₂ A → M₂ (StateM s₁) (StateM s₂) A
