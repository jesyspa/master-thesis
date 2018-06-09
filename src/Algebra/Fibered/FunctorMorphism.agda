module Algebra.Fibered.FunctorMorphism where

open import ThesisPrelude
open import Algebra.Fibered.FiberedSet

module _ {I J : Set}(F : FiberedSet I → FiberedSet I)
                    (G : FiberedSet J → FiberedSet J)
                    (ri : I → J) where
  record FiberedFunctorMorphism : Set₁ where
    field
      RunFFM : {!∀{A B} → (A →ᶠ B)!}
