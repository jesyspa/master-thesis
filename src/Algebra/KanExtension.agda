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

lan-factorise : ∀{φ ψ} → φ ⇒ (ψ ∘′ f) → Lan φ ⇒ ψ
lan-factorise nt (s′ , refl , v) = nt v

Ran : (S′ → Set (l ⊔ l′)) → S → Set (l ⊔ l′)
Ran φ s = ∀ s′ → f s′ ≡ s → φ s′

Ran* : {φ φ′ : S′ → Set (l ⊔ l′)}
     → φ ⇒ φ′
     → Ran φ ⇒ Ran φ′
Ran* nt {s} r s′ refl = nt (r s′ refl)

Rε : ∀{φ} → (Ran φ ∘′ f) ⇒ φ
Rε {s = s′} r = r s′ refl

ran-factorise : ∀{φ ψ} → (φ ∘′ f) ⇒ ψ → φ ⇒ Ran ψ
ran-factorise nt {s = s′} v t′ refl = nt v
