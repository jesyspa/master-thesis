module Algebra.BinaryRelation where

open import ThesisPrelude
open import Algebra.Proposition

module _ (A B : Set) where
  record BinaryRelation : Set₁ where
    field
      Relation-BR : A → B → Set
      IsProp-BR : ∀ a b → IsProposition (Relation-BR a b)
      
open BinaryRelation

id-BR : ∀{A} → BinaryRelation A A
Relation-BR id-BR = _≡_
IsProp-BR   id-BR a b refl refl = refl

module _ {A B C} where
  comp-BR : BinaryRelation A B → BinaryRelation B C → BinaryRelation A C
  Relation-BR (comp-BR br₁ br₂) a c = Σ B λ b → Relation-BR br₁ a b × Relation-BR br₂ b c
  -- Oh, oops, this isn't provable.
  IsProp-BR (comp-BR br₁ br₂) a c (b₁ , pf₁) (b₂ , pf₂) = {!!}
