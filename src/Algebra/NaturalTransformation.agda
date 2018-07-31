module Algebra.NaturalTransformation where

open import ThesisPrelude
open import Algebra.Function

_⇒_ : ∀{l l′}{S : Set l}(φ φ′ : S → Set l′) → Set (l ⊔ l′)
φ ⇒ φ′ = ∀{s} → φ s → φ′ s
