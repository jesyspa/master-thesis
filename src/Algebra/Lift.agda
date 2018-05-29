module Algebra.Lift {l l′} where

open import ThesisPrelude

record Lift (A : Set l′) : Set (l ⊔ l′) where
  constructor lift
  field lower : A
open Lift

lift-map : ∀{A B : Set l′}
         → (A → B)
         → Lift A → Lift B
lift-map f = lift ∘′ f ∘′ lower
