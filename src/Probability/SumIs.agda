open import Probability.Class
module Probability.SumIs (Q : Set){{PQ : Probability Q}} where

open import ThesisPrelude
open import Algebra.FiniteSet


module _ (I : Set){{ULI : UniqueListable I}} where
  open UniqueListable ULI
  open Listable super-Enumeration
  data SumIs (f : I → Q)(q : Q) : Set where
    SumIs-prf : q ≡ sum (map f ListEnumeration) → SumIs f q
