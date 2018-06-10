open import Algebra.Fibered.FiberedSet
module Algebra.Fibered.FunctorMorphism {I J : Set}(ri : I → J)
                                       (F : FiberedSet I → FiberedSet I)
                                       (G : FiberedSet J → FiberedSet J) where

open import ThesisPrelude

record FiberedFunctorMorphism : Set₁ where
  field
    RunFFM : ∀{X Y} → RefiberingArrow ri X Y → RefiberingArrow ri (F X) (G Y)
