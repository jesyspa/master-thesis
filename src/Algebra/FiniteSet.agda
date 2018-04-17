module Algebra.FiniteSet {l}(A : Set l) where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List
open import Utility.Num

record FiniteSet : Set l where
  field
    SizeBound     : Nat
    Enumeration   : Fin SizeBound → A
    IsEnumeration : Surjective Enumeration
open FiniteSet

record Listable : Set l where
  field
    ListEnumeration : List A
    IsComplete      : (a : A) → a ∈ ListEnumeration
open Listable

enumerateFin : ∀ n → List (Fin n)
enumerateFin zero = []
enumerateFin (suc n) = zero ∷ map suc (enumerateFin n)

enumerateFin-complete : ∀ n → (k : Fin n) → k ∈ enumerateFin n
enumerateFin-complete zero ()
enumerateFin-complete (suc n) zero = here zero _
enumerateFin-complete (suc n) (suc k) = there (suc k) _ _ (map-preserves-in suc _ _ (enumerateFin-complete n k))

decide-equality : Listable → (a b : A) → Dec (a ≡ b)
decide-equality LA a b with elem-index (IsComplete LA a) == elem-index (IsComplete LA b)
decide-equality LA a b  | yes eq with elem-index-Inj eq
decide-equality LA a .a | yes eq | refl , _ = yes refl
decide-equality LA a b  | no neq = no λ { refl → neq refl }

ListableDecEq : Listable → Eq A
_==_ {{ListableDecEq LA}} = decide-equality LA

record UniqueListable : Set l where
  field
    overlap {{super-Enumeration}} : Listable 
    IsUnique        : (a : A)(p : a ∈ ListEnumeration super-Enumeration) → p ≡ IsComplete super-Enumeration a 
open UniqueListable

ListableUniqueEnumeration : Listable → Listable 
ListEnumeration (ListableUniqueEnumeration LA)   = uniques {{ListableDecEq LA}} (ListEnumeration LA)
IsComplete      (ListableUniqueEnumeration LA) a = unique-preserves-elem {{ListableDecEq LA}} _ _ (IsComplete LA a)


