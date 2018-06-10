open import Algebra.Fibered.FiberedSet
module Algebra.Fibered.Monad {I : Set}(F : FiberedSet I → FiberedSet I)  where

open import ThesisPrelude
open import Algebra.Fibered.Functor

record FiberedMonad : Set₁ where
  field
    overlap {{super-functorᶠ}} : FiberedFunctor F
    returnᶠ : ∀{A} → (A →ᶠ F A)
    -- It would be interesting to rewrite this to have the usual order of parameters,
    -- but it's not clear to me how this is possible.
    bindᶠ  : ∀{A B} → (A →ᶠ F B) → (F A →ᶠ F B)
