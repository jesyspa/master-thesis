module Algebra.NaturalTransformation where

open import ThesisPrelude
open import Algebra.Function

_⇒_ : ∀{S : Set}(φ φ′ : S → Set) → Set
φ ⇒ φ′ = ∀{s} → φ s → φ′ s
