open import ThesisPrelude
module Algebra.Indexed.MonadMorphismCat where

open import Algebra.Function
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open IxMonad
open IxMonadMorphism

module _ {l l′}{S : Set l}{M : (S → Set l′) → S → Set l′}{{IMM : IxMonad M}} where
  id-IxMM : IxMonadMorphism M M {l}
  StateM id-IxMM = _≡_
  TermM  id-IxMM conn refl = fmapⁱ IMM (get-fun (conn refl))

module _ {l₁ l₂ l₃ l′}{S₁ : Set l₁}{S₂ : Set l₂}{S₃ : Set l₃}
         {M₁ : (S₁ → Set l′) → S₁ → Set l′}{{IMM₁ : IxMonad M₁}}
         {M₂ : (S₂ → Set l′) → S₂ → Set l′}{{IMM₂ : IxMonad M₂}}
         {M₃ : (S₃ → Set l′) → S₃ → Set l′}{{IMM₃ : IxMonad M₃}} where
  comp-IxMM : ∀{i₁ i₂} → IxMonadMorphism M₁ M₂ {i₁} → IxMonadMorphism M₂ M₃ {i₂} → IxMonadMorphism M₁ M₃ {i₁ ⊔ i₂ ⊔ l₂}
  StateM (comp-IxMM mm mn) s₁ s₃ = Σ S₂ λ s₂ → StateM mm s₁ s₂ × StateM mn s₂ s₃
  TermM  (comp-IxMM mm mn) conn (s₂ , pf₁ , pf₂) = TermM mn {!!} {!!} ∘′ TermM mm {!!} {!!}

