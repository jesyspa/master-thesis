open import ThesisPrelude
module Utility.List.CountProps {l}{A : Set l}{{_ : Eq A}} where

open import Utility.List.Elem
open import Utility.List.Functions

count-not-in : (xs : List A)(a : A)
             → ¬ (a ∈ xs)
             → 0 ≡ count xs a
count-not-in [] a nin = refl
count-not-in (x ∷ xs) a nin with a == x
... | yes refl = ⊥-elim (nin (here _ _))
... | no   neq = count-not-in xs a (nin ∘′ there _ _ _)
