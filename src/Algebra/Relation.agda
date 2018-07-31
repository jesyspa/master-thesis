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
