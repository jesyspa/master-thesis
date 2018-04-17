module Algebra.FiniteSetExtensions {l}{A : Set l} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.FiniteSet A
open import Utility.List
open import Utility.Num

open FiniteSet {{...}}
open Listable {{...}}
open UniqueListable

instance
  FiniteSetListable : {{_ : FiniteSet}} → Listable
  ListEnumeration {{FiniteSetListable}} = map Enumeration (enumerateFin SizeBound) 
  IsComplete      {{FiniteSetListable}} a with IsEnumeration a
  ... | k , refl = map-preserves-in Enumeration k _ (enumerateFin-complete _ k) 

instance
  ListableDecEq′ = ListableDecEq

instance
  ListableUniqueListable : Listable → UniqueListable 
  super-Enumeration (ListableUniqueListable LA)     = ListableUniqueEnumeration LA
  IsUnique          (ListableUniqueListable LA) a p = uniques-unique {{ListableDecEq LA}} _ _ (IsComplete {{LA}} a) p
