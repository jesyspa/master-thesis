module Algebra.Parametrised.Monad where

open import ThesisPrelude

record ParMonad {l l′}(𝑺 : Set l′)(M : 𝑺 → 𝑺 → Set l → Set l) : Set (lsuc l ⊔ l′) where
  infixl 1 _>>=ᵖ_
  field
    returnᵖ : ∀{S A} → A → M S S A
    _>>=ᵖ_ : ∀{S₀ S₁ S₂ A B} → M S₀ S₁ A → (A → M S₁ S₂ B) → M S₀ S₂ B
    overlap {{super-functor}} : ∀{S S′} → Functor (M S S′)

open ParMonad {{...}} public

