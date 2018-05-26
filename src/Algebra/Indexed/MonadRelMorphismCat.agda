open import ThesisPrelude
module Algebra.Indexed.MonadRelMorphismCat where

open import Algebra.Function
open import Algebra.Relation
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadRelMorphism

open IxMonadRelMorphism

module _ {S : Set}{M : (S → Set) → S → Set}{{IMM : IxMonad M}} where
  open IxMonad IMM
  id-IxMRM : IxMonadRelMorphism M M _≡_
  TermRM  id-IxMRM refl f m = fmapⁱ (f refl) m

module _ {S₁ S₂ S₃ : Set}
         {M₁ : (S₁ → Set) → S₁ → Set}{{IMM₁ : IxMonad M₁}}
         {M₂ : (S₂ → Set) → S₂ → Set}{{IMM₂ : IxMonad M₂}}
         {M₃ : (S₃ → Set) → S₃ → Set}{{IMM₃ : IxMonad M₃}}
         {R₁ : Relation S₁ S₂}{R₂ : Relation S₂ S₃} where
  open IxMonad {{...}}
  comp-IxMRM : IxMonadRelMorphism M₁ M₂ R₁ → IxMonadRelMorphism M₂ M₃ R₂ → IxMonadRelMorphism M₁ M₃ (comp-R R₁ R₂)
  TermRM  (comp-IxMRM mm mn) {A₁} {A₃} (s₁ , p₁ , p₂) f m = TermRM mn p₂ f₂ (TermRM mm p₁ f₁ m)
    where
      A₂ : S₂ → Set
      A₂ s₂ = Σ S₁ λ s₁ → R₁ s₁ s₂ × A₁ s₁
      f₁ : ∀{t₁ t₂} → R₁ t₁ t₂ → A₁ t₁ → A₂ t₂
      f₁ q₁ a = _ , q₁ , a
      f₂ : ∀{t₂ t₃} → R₂ t₂ t₃ → A₂ t₂ → A₃ t₃
      f₂ q₂ (t₁ , q₁ , a) = f (_ , q₁ , q₂) a
