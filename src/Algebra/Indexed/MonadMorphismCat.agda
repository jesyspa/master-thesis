open import ThesisPrelude
module Algebra.Indexed.MonadMorphismCat where

open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open IxMonad
open IxMonadMorphism

module _ {l l′}{S : Set l}{M : (S → Set l′) → S → Set l′} where
  id-IxMM : IxMonadMorphism M M
  StateM id-IxMM = id
  TermM  id-IxMM = id

module _ {l₁ l₂ l₃ l′}{S₁ : Set l₁}{S₂ : Set l₂}{S₃ : Set l₃}
         {M₁ : (S₁ → Set l′) → S₁ → Set l′}
         {M₂ : (S₂ → Set l′) → S₂ → Set l′}
         {M₃ : (S₃ → Set l′) → S₃ → Set l′}{{_ : IxMonad M₃}} where
  comp-IxMM : IxMonadMorphism M₁ M₂ → IxMonadMorphism M₂ M₃ → IxMonadMorphism M₁ M₃
  StateM (comp-IxMM mm mn) = StateM mm ∘′ StateM mn
  TermM  (comp-IxMM mm mn) m = TermM mn (TermM mm m) 
