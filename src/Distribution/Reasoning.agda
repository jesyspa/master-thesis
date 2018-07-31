open import Distribution.Class using (DistMonad)
open import Distribution.PropsClass using (DistMonadProps)
module Distribution.Reasoning (F : Set → Set){{DF : DistMonad F}}{{DPF : DistMonadProps F}} where

open DistMonad DF
open DistMonadProps DPF

open import ThesisPrelude
open import Probability.Class
open import Algebra.MonadProps F
open import Algebra.ApplicativeProps F
open import Algebra.FunctorProps F
open import Utility.Vector
open import Algebra.Function
open import Algebra.LiftingProps F
open import Probability.PropsClass (probability)

module _ {A : Set}{{_ : Eq A}} where
  refl-D : {D : F A} → D ≡D D
  refl-D = sample-equiv λ a → refl
  
  sym-D : {D₁ D₂ : F A} → D₁ ≡D D₂ → D₂ ≡D D₁
  sym-D p = sample-equiv (sym ∘ sample-invariant p)
  
  trans-D : {D₁ D₂ D₃ : F A} → D₁ ≡D D₂ → D₂ ≡D D₃ → D₁ ≡D D₃
  trans-D p q = sample-equiv λ a → sample-invariant p a ⟨≡⟩ sample-invariant q a

  lift-D-eq : {D₁ D₂ : F A} → D₁ ≡ D₂ → D₁ ≡D D₂
  lift-D-eq refl = refl-D

  _⟨≡D⟩_ = trans-D

  _⟨≡D⟩ʳ_ : {D₁ D₂ D₃ : F A} → D₁ ≡D D₂ → D₃ ≡D D₂ → D₁ ≡D D₃
  p ⟨≡D⟩ʳ q = p ⟨≡D⟩ sym-D q

  _ʳ⟨≡D⟩_ : {D₁ D₂ D₃ : F A} → D₂ ≡D D₁ → D₂ ≡D D₃ → D₁ ≡D D₃
  p ʳ⟨≡D⟩ q = sym-D p ⟨≡D⟩ q

  _ʳ⟨≡D⟩ʳ_ : {D₁ D₂ D₃ : F A} → D₂ ≡D D₁ → D₃ ≡D D₂ → D₁ ≡D D₃
  p ʳ⟨≡D⟩ʳ q = sym-D p ⟨≡D⟩ sym-D q

  infixr 0 distEqReasoningStep distEqReasoningStepʳ
  infixr 0 distEqReasoningStepˡ distEqReasoningStepˡʳ
  infixr 1 _∎D

  syntax distEqReasoningStep x q p = x ≡D⟨ p ⟩ q
  distEqReasoningStep : ∀(D₁ : F A){D₂ D₃} → D₂ ≡D D₃ → D₁ ≡D D₂ → D₁ ≡D D₃
  D₁ ≡D⟨ p ⟩ q = p ⟨≡D⟩ q

  syntax distEqReasoningStepʳ x q p = x ≡D⟨ p ⟩ʳ q
  distEqReasoningStepʳ : ∀(D₁ : F A){D₂ D₃} → D₂ ≡D D₃ → D₂ ≡D D₁ → D₁ ≡D D₃
  D₁ ≡D⟨ p ⟩ʳ q = p ʳ⟨≡D⟩ q

  syntax distEqReasoningStepˡ x q p = x ≡D⟨ p ⟩ˡ q
  distEqReasoningStepˡ : ∀(D₁ : F A){D₂ D₃} → D₂ ≡D D₃ → D₁ ≡ D₂ → D₁ ≡D D₃
  D₁ ≡D⟨ p ⟩ˡ q = lift-D-eq p ⟨≡D⟩ q

  syntax distEqReasoningStepˡʳ x q p = x ≡D⟨ p ⟩ˡʳ q
  distEqReasoningStepˡʳ : ∀(D₁ : F A){D₂ D₃} → D₂ ≡D D₃ → D₂ ≡ D₁ → D₁ ≡D D₃
  D₁ ≡D⟨ p ⟩ˡʳ q = lift-D-eq p ʳ⟨≡D⟩ q

  _∎D : (D : F A) → D ≡D D
  D ∎D = refl-D
