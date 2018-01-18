import ThesisPrelude as TP
module Utility.List.Elem.Decidable {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition

decide-elem : (a : A) (xs : List A) → Dec (a ∈ xs)
decide-elem a [] = no λ ()
decide-elem a (x ∷ xs) with a == x
... | yes refl = yes (here a xs)
... | no neq with decide-elem a xs
... | yes p = yes (there a x xs p)
... | no np = no f
  where f : ¬ (a ∈ x ∷ xs)
        f (here _ _) = neq refl
        f (there _ _ _ p) = np p
