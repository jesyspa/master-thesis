module Algebra.FiniteSet where

open import ThesisPrelude
open import Utility.Vector
open import Algebra.Function
open import Utility.List
open import Utility.Num

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

elem-index : ∀{l}{A : Set l}{a}{xs : List A} → a ∈ xs → Nat
elem-index (here x xs) = zero
elem-index (there x y xs p) = suc (elem-index p)

elem-index-Inj : ∀{l}{A : Set l}{a b}{xs : List A}{p : a ∈ xs}{q : b ∈ xs}
               → elem-index p ≡ elem-index q
               → Σ (a ≡ b) λ eq → transport (λ x → x ∈ xs) eq p ≡ q
elem-index-Inj {p = here a xs}      {here .a .xs} refl    = refl , refl
elem-index-Inj {p = here a xs}      {there b .a .xs q}    ()
elem-index-Inj {p = there a y xs p} {here .y .xs}         ()
elem-index-Inj {p = there a y xs p} {there b .y .xs q} eq with elem-index-Inj (suc-Inj eq)
... | refl , refl = refl , refl

-- According to Firsov & Uustalu, this is provable
decide-equality : ∀{A} → Listable A → (a b : A) → Dec (a ≡ b)
decide-equality LA a b with elem-index (IsComplete LA a) == elem-index (IsComplete LA b)
decide-equality LA a b  | yes eq with elem-index-Inj eq
decide-equality LA a .a | yes eq | refl , z′ = yes refl
decide-equality LA a b  | no neq = no λ { refl → neq refl }

DecEquality : ∀ A {{_ : Listable A}} → Eq A
_==_ {{DecEquality A {{LA}}}} = decide-equality LA
