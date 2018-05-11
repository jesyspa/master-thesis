module Algebra.Lift where

open import ThesisPrelude

record Lift {l l′} (A : Set l′) : Set (l ⊔ l′) where
  constructor lift
  field lower : A
open Lift

lift-map : ∀{l l′}{A B : Set l′}
         → (A → B)
         → Lift {l} A → Lift {l} B
lift-map f = lift ∘′ f ∘′ lower
