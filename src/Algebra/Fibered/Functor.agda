open import Algebra.Fibered.FiberedSet
module Algebra.Fibered.Functor {I : Set}(F : FiberedSet I → FiberedSet I)  where

open import ThesisPrelude

record FiberedFunctor : Set₁ where
  field
    fmapᶠ : ∀{A A′} → (A →ᶠ A′) → (F A →ᶠ F A′)
