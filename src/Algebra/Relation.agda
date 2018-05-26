module Algebra.Relation where

open import ThesisPrelude

Relation : Set → Set → Set₁
Relation S₁ S₂ = S₁ → S₂ → Set

module _ {S} where
  id-R : Relation S S
  id-R = _≡_

module _ {S₁ S₂ S₃} where
  comp-R : Relation S₁ S₂ → Relation S₂ S₃ → Relation S₁ S₃
  comp-R R₁ R₂ s₁ s₃ = Σ S₂ λ s₂ → R₁ s₁ s₂ × R₂ s₂ s₃

module _ {S₁ S₂} where
  incL-R : Relation S₁ (S₁ × S₂)
  incL-R s₁ (s₁′ , s₂) = s₁ ≡ s₁′

  incR-R : Relation S₂ (S₁ × S₂)
  incR-R s₂ (s₁ , s₂′) = s₂ ≡ s₂′

module _ {S₁ S₂ T₁ T₂} where
  parcomp-R : Relation S₁ T₁ → Relation S₂ T₂ → Relation (S₁ × S₂) (T₁ × T₂)
  parcomp-R R₁ R₂ (s₁ , s₂) (t₁ , t₂) = R₁ s₁ t₁ × R₂ s₂ t₂
