module Algebra.FiniteSet where

open import ThesisPrelude
open import Utility.Vector
open import Algebra.Function
open import Utility.List

record FiniteSet (A : Set) : Set where
  field
    SizeBound     : Nat
    Enumeration   : BitVec SizeBound → A
    IsEnumeration : Surjective Enumeration
open FiniteSet

vec-finite : ∀ n → FiniteSet (BitVec n)
SizeBound     (vec-finite n) = n
Enumeration   (vec-finite n) bv = bv
IsEnumeration (vec-finite n) bv = bv , refl

record Listable (A : Set) : Set where
  field
    ListEnumeration : List A
    IsComplete      : (a : A) → a ∈ ListEnumeration
open Listable

FiniteSetsListable : ∀{A} → FiniteSet A → Listable A
ListEnumeration (FiniteSetsListable fs) = map (Enumeration fs) (all-bitvecs $ SizeBound fs) 
IsComplete      (FiniteSetsListable fs) a with IsEnumeration fs a
... | v , refl = map-preserves-in (Enumeration fs) v (all-bitvecs $ SizeBound fs) (all-bitvecs-complete v)

-- According to Firsov & Uustalu, this is provable
DecEquality : ∀ A {{_ : Listable A}} → Eq A
_==_ {{DecEquality A {{LA}}}} x y = ?
