open import Algebra.Fibered.FiberedSet
module Algebra.Fibered.Monad {I : Set}(F : FiberedSet I → FiberedSet I)  where

open import ThesisPrelude
open import Algebra.Fibered.Functor

record FiberedMonad : Set₁ where
  infixl 1 _>>=ᶠ_
  field
    overlap {{super-functorᶠ}} : FiberedFunctor F
    returnᶠ : ∀{A} → (A →ᶠ F A)
    _>>=ᶠ_  : ∀{A} → (A →ᶠ F A)
