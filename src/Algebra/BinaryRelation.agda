module Algebra.BinaryRelation where

open import ThesisPrelude
open import Algebra.Proposition

module _ {l l′}{A : Set l}{B : Set l′} where
  record BinaryRelation (R : A → B → Set) : Set (l ⊔ l′) where
    field
      IsProp-BR : ∀ a b → IsProposition (R a b)
      
