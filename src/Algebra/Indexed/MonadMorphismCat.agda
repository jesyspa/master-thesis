open import ThesisPrelude
module Algebra.Indexed.MonadMorphismCat where

open import Algebra.Function
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open IxMonad
open IxMonadMorphism
open IxMonadComorphism

module _ {l l′}{S : Set l}{M : (S → Set l′) → S → Set l′}{{IMM : IxMonad M}} where
  id-IxMM : IxMonadMorphism M M
  StateM id-IxMM = id
  TermM  id-IxMM = id

  id-IxMCM : IxMonadComorphism M M
  StateCM id-IxMCM = id
  TermCM  id-IxMCM = id

module _ {l₁ l₂ l₃ l′}{S₁ : Set l₁}{S₂ : Set l₂}{S₃ : Set l₃}
         {M₁ : (S₁ → Set l′) → S₁ → Set l′}{{IMM₁ : IxMonad M₁}}
         {M₂ : (S₂ → Set l′) → S₂ → Set l′}{{IMM₂ : IxMonad M₂}}
         {M₃ : (S₃ → Set l′) → S₃ → Set l′}{{IMM₃ : IxMonad M₃}} where
  comp-IxMM : IxMonadMorphism M₁ M₂ → IxMonadMorphism M₂ M₃ → IxMonadMorphism M₁ M₃
  StateM (comp-IxMM mm mn) = StateM mn ∘′ StateM mm
  TermM  (comp-IxMM mm mn) = TermM mn ∘′ TermM mm

  comp-IxMCM : IxMonadComorphism M₁ M₂ → IxMonadComorphism M₂ M₃ → IxMonadComorphism M₁ M₃
  StateCM (comp-IxMCM mm mn) = StateCM mm ∘′ StateCM mn
  TermCM  (comp-IxMCM mm mn) = TermCM mn ∘′ TermCM mm
