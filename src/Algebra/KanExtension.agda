open import Algebra.Function
module Algebra.KanExtension {l l′}{S : Set l}{S′ : Set l′}(f : S′ → S) where

open import ThesisPrelude
open import Algebra.NaturalTransformation

Lan : (S′ → Set (l ⊔ l′)) → S → Set (l ⊔ l′)
Lan φ s = Σ S′ λ s′ → (f s′ ≡ s) × φ s′

Lan* : {φ φ′ : S′ → Set (l ⊔ l′)}
     → φ ⇒ φ′
     → Lan φ ⇒ Lan φ′
Lan* mf (s′ , eq , v) = s′ , eq , mf v

Lε : ∀{φ} → φ ⇒ (Lan φ ∘′ f)
Lε v = _ , refl , v

factorise : ∀{φ ψ} → φ ⇒ (ψ ∘′ f) → (Lan φ ∘′ f) ⇒ (ψ ∘′ f)
factorise nt (s′ , eq , v) rewrite sym eq = nt v
