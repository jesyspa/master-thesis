open import Probability.Class
module Probability.SumIs (Q : Set){{PQ : Probability Q}} where

open import ThesisPrelude
open import Algebra.FiniteSet
open import Algebra.FiniteSetInstances
open import Utility.List


module _ {l}(I : Set l){{ULI : UniqueListable I}} where
  open UniqueListable ULI
  open Listable super-Enumeration
  data SumIs (f : I → Q)(q : Q) : Set where
    SumIs-prf : q ≡ sum (map f ListEnumeration) → SumIs f q

  SumIs-ext : (f g : I → Q)(q : Q) → (∀ i → f i ≡ g i) → SumIs f q → SumIs g q
  SumIs-ext f g q eq (SumIs-prf refl) = SumIs-prf $ cong sum $ map-ext f g eq ListEnumeration

module _ {l}{A : Set l}(xs : List A) where
  ElemSumIs : (f : A → Q)(q : Q) → Set
  ElemSumIs f q = SumIs (Elem xs) (f ∘′ fst) q

  ElemSumIs-match : (f : A → Q)(q : Q) → ElemSumIs f q → q ≡ sum (map f xs)
  ElemSumIs-match f q (SumIs-prf eq) rewrite eq | sym (list-elements-map xs f) = refl

  ElemSum-lem : (f : A → Q)(q : Q) → ElemSumIs 
