module Probability.Abstract where

open import ThesisPrelude
open import Probability.Class

abstract
  data AProbability : Set where

postulate
  instance
    AProbabilitySemiring : Semiring AProbability
    AProbabilityOrd : Ord AProbability
    AProbabilityProbabilityProps : ProbabilityProps AProbability
