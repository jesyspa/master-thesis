module Algebra.FiniteSetInstances where

open import ThesisPrelude
open import Utility.List.Elem

module _ {l}{A : Set l}{xs : List A} where
  open import Algebra.FiniteSet (Elem xs)
  open Listable
  open UniqueListable
  instance
    ListableElem : Listable
    ListEnumeration ListableElem   = list-elements xs
    IsComplete      ListableElem e = list-elements-Complete xs e

    UniqueListableElem : UniqueListable
    super-Enumeration UniqueListableElem     = ListableElem
    IsUnique          UniqueListableElem a p = list-elements-Unique xs a p
