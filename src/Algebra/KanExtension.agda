module Algebra.KanExtension where

open import ThesisPrelude
open import Algebra.Function

_⇒_ : ∀{S : Set}(φ φ′ : S → Set) → Set
φ ⇒ φ′ = ∀{s} → φ s → φ′ s

module _ {S S′ : Set}(f : S′ → S){{If : Injective f}} where
  Lan : (S′ → Set) → S → Set
  Lan φ s = Σ S′ λ s′ → (f s′ ≡ s) × φ s′

  Lan* : {φ φ′ : S′ → Set}
       → φ ⇒ φ′
       → Lan φ ⇒ Lan φ′
  Lan* mf (s′ , eq , v) = s′ , eq , mf v

  Lε : ∀{φ} → φ ⇒ (Lan φ ∘′ f)
  Lε v = _ , refl , v

  factorise : ∀{φ ψ} → φ ⇒ (ψ ∘′ f) → (Lan φ ∘′ f) ⇒ (ψ ∘′ f)
  factorise nt (s′ , eq , v) with If eq
  factorise nt (s′ , eq , v) | refl = nt v
