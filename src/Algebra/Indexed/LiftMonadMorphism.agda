open import ThesisPrelude
module Algebra.Indexed.LiftMonadMorphism {l}(M : Set l → Set l){{_ : Monad M}} where

open import Algebra.Indexed.LiftMonad M
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open IxMonad {{...}}
open IxMonadMorphism

module _ {l₁′ l₂′}{S₁ : Set l₁′}{S₂ : Set l₂′}(f : S₁ → S₂) where
  LiftMMorphism : IxMonadMorphism (LiftM {S = S₁}) (LiftM {S = S₂})
  StateM LiftMMorphism = f
  TermM  LiftMMorphism m = m
