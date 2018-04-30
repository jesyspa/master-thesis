module Algebra.FiniteSet where

open import ThesisPrelude
open import Utility.Vector
open import Algebra.Function
open import Algebra.Equality
open import Utility.List
open import Utility.Num

record FiniteSet (A : Set) : Set where
  field
    SizeBound     : Nat
    Enumeration   : BitVec SizeBound → A
    IsEnumeration : Surjective Enumeration
open FiniteSet

VecFinite : ∀ n → FiniteSet (BitVec n)
SizeBound     (VecFinite n) = n
Enumeration   (VecFinite n) bv = bv
IsEnumeration (VecFinite n) bv = bv , refl

record Listable (A : Set) : Set where
  field
    ListEnumeration : List A
    IsComplete      : (a : A) → a ∈ ListEnumeration
open Listable

instance
  FiniteSetListable : ∀{A}{{_ : FiniteSet A}} → Listable A
  ListEnumeration (FiniteSetListable {{FS}}) = map (Enumeration FS) (all-bitvecs $ SizeBound FS) 
  IsComplete      (FiniteSetListable {{FS}}) a with IsEnumeration FS a
  ... | v , refl = map-preserves-in (Enumeration FS) v (all-bitvecs $ SizeBound FS) (all-bitvecs-complete v)

decide-equality : ∀{A} → Listable A → (a b : A) → Dec (a ≡ b)
decide-equality LA a b with elem-index (IsComplete LA a) == elem-index (IsComplete LA b)
decide-equality LA a b  | yes eq with elem-index-Inj eq
decide-equality LA a .a | yes eq | refl , _ = yes refl
decide-equality LA a b  | no neq = no λ { refl → neq refl }

instance
  ListableDecEq : ∀{A} → Listable A → Eq A
  _==_ {{ListableDecEq LA}} = decide-equality LA

record UniqueListable (A : Set) : Set where
  field
    overlap {{super-Enumeration}} : Listable A
    IsUnique        : (a : A)(p : a ∈ ListEnumeration super-Enumeration) → p ≡ IsComplete super-Enumeration a 
  UniqueListEnumeration : List A
  UniqueListEnumeration = ListEnumeration super-Enumeration
open UniqueListable

ListableUniqueEnumeration : ∀{A} → Listable A → Listable A
ListEnumeration (ListableUniqueEnumeration LA)   = uniques {{ListableDecEq LA}} (ListEnumeration LA)
IsComplete      (ListableUniqueEnumeration LA) a = unique-preserves-elem {{ListableDecEq LA}} _ _ (IsComplete LA a)

ListableUniqueListable : ∀{A} → Listable A → UniqueListable A
super-Enumeration (ListableUniqueListable LA)     = ListableUniqueEnumeration LA
IsUnique          (ListableUniqueListable LA) a p = uniques-unique {{ListableDecEq LA}} _ _ (IsComplete LA a) p

private
  unique-list-lem : ∀{l}{A : Set l}{{_ : Eq A}}(xs : List A)(a : A)
                  → (pt : a ∈ xs)
                  → (∀ pt′ → pt′ ≡ pt)
                  → one ≡ count xs a
  unique-list-lem [] a () pf
  unique-list-lem (x ∷ xs) .x (here .x .xs) pf with x == x
  ... | yes refl = cong suc lem
    where lem : 0 ≡ count xs x
          lem with decide-elem x xs
          lem | yes pt′ with pf (there _ _ _ pt′)
          lem | yes pt′ | ()
          lem | no  npt = count-not-in xs x npt
  ... | no neq = ⊥-elim (neq refl)
  unique-list-lem (x ∷ xs) a  (there .a .x .xs pt) pf with a == x
  unique-list-lem (x ∷ xs) a  (there .a .x .xs pt) pf | yes refl with pf (here _ _)
  ... | ()
  unique-list-lem (x ∷ xs) a  (there .a .x .xs pt) pf | no  neq  = unique-list-lem xs a pt (there-Inj ∘ pf ∘ there _ _ _)

unique-list-gives-count-one : ∀{A}{{ULA : UniqueListable A}} a → one ≡ count (UniqueListEnumeration ULA) a
unique-list-gives-count-one {{ULA}} a = unique-list-lem (UniqueListEnumeration ULA) a (IsComplete (super-Enumeration ULA) a) (IsUnique ULA a)

module _ A {{FSA : FiniteSet A}} where
  private
    ULA : UniqueListable A
    ULA = ListableUniqueListable FiniteSetListable
  finite-set-list : List A
  finite-set-list = ListEnumeration (super-Enumeration ULA)
  
  finite-set-list-complete : (a : A) → a ∈ finite-set-list
  finite-set-list-complete = IsComplete (super-Enumeration ULA)
  
  finite-set-list-unique : (a : A)(p : a ∈ finite-set-list) → p ≡ finite-set-list-complete a
  finite-set-list-unique = IsUnique ULA 

VecListable : ∀ n → Listable (BitVec n)
ListEnumeration (VecListable n) = all-bitvecs n
IsComplete      (VecListable n) = all-bitvecs-complete 

VecUniqueListable : ∀ n → UniqueListable (BitVec n)
super-Enumeration (VecUniqueListable n) = VecListable n
IsUnique          (VecUniqueListable n) = all-bitvecs-unique 

