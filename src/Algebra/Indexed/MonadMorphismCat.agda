open import ThesisPrelude
module Algebra.Indexed.MonadMorphismCat where

open import Algebra.Function
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open IxMonad
open IxMonadMorphism
open IxMonadComorphism

module _ {l l′}{S : Set l}{M : (S → Set l′) → S → Set l′}{{IMM : IxMonad M}} where
  id-IxMM : IxMonadMorphism M M id
  RunIxMM id-IxMM = id

  id-IxMCM : IxMonadComorphism M M id
  RunIxMCM id-IxMCM = id

module _ {l₁ l₂ l₃ l′}{S₁ : Set l₁}{S₂ : Set l₂}{S₃ : Set l₃}
         {M₁ : (S₁ → Set l′) → S₁ → Set l′}{{IMM₁ : IxMonad M₁}}
         {M₂ : (S₂ → Set l′) → S₂ → Set l′}{{IMM₂ : IxMonad M₂}}
         {M₃ : (S₃ → Set l′) → S₃ → Set l′}{{IMM₃ : IxMonad M₃}} where
  comp-IxMM : ∀{f g} → IxMonadMorphism M₁ M₂ f → IxMonadMorphism M₂ M₃ g → IxMonadMorphism M₁ M₃ (g ∘′ f)
  RunIxMM  (comp-IxMM mm mn) = RunIxMM mn ∘′ RunIxMM mm

  comp-IxMCM : ∀{f g} → IxMonadComorphism M₁ M₂ f → IxMonadComorphism M₂ M₃ g → IxMonadComorphism M₁ M₃ (f ∘′ g)
  RunIxMCM  (comp-IxMCM mm mn) = RunIxMCM mn ∘′ RunIxMCM mm
