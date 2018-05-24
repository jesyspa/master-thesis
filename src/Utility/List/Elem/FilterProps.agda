import ThesisPrelude as TP
module Utility.List.Elem.FilterProps {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.ExactSize
open import Algebra.Equality
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Filter

filter-does-not-add-elements-Inj : (a : A)(xs : List A)(pd : A → Bool)
                                 → Injective (filter-does-not-add-elements a xs pd)
filter-does-not-add-elements-Inj a [] pd {()} {()} eq
filter-does-not-add-elements-Inj a (x ∷ xs) pd {p} {q} eq with pd x
filter-does-not-add-elements-Inj .x (x ∷ xs) pd {here .x ._} {here .x ._} eq | true = refl
filter-does-not-add-elements-Inj .x (x ∷ xs) pd {here .x ._} {there .x .x ._ q} () | true
filter-does-not-add-elements-Inj a (.a ∷ xs) pd {there .a .a ._ p} {here .a ._} () | true
filter-does-not-add-elements-Inj a (x ∷ xs) pd {there .a .x ._ p} {there .a .x ._ q} eq | true
  = cong (there a x (filter pd xs)) (filter-does-not-add-elements-Inj a xs pd (there-Inj eq))
... | false = filter-does-not-add-elements-Inj a xs pd (there-Inj eq)

filter-preserves-Ret : (a : A)(xs : List A)(pd : A → Bool)(pf : IsTrue (pd a))
                     → Retraction filter-does-not-add-elements a xs pd of filter-preserves-satisfying a xs pd pf
filter-preserves-Ret a .(a ∷ xs) pd pf (here .a xs) with pd a
filter-preserves-Ret a .(a ∷ xs) pd () (here .a xs) | false
filter-preserves-Ret a .(a ∷ xs) pd true (here .a xs) | true = refl
filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) with pd y
filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) | false = cong (there a y xs) $ filter-preserves-Ret a xs pd pf p
filter-preserves-Ret a .(y ∷ xs) pd pf (there .a y xs p) | true = cong (there a y xs) $ filter-preserves-Ret a xs pd pf p

if-not-a-then-nothing : (a : A) (xs : List A)
                      → ¬ (a ∈ filter-is a xs) → [] ≡ filter-is a xs
if-not-a-then-nothing a [] np = refl
if-not-a-then-nothing a (x ∷ xs) np with a == x
... | yes refl = ⊥-elim $ np (here a (filter (isYes ∘ (_==_ a)) xs)) 
... | no eq = if-not-a-then-nothing a xs np

if-not-there-filter-empty : (a : A) (xs : List A)
                          → ¬ (a ∈ xs) → [] ≡ filter-is a xs
if-not-there-filter-empty a xs np = if-not-a-then-nothing a xs λ p → np (equalFilter-inv a xs p) 

if-not-there-filter-equal : (a : A)(xs : List A)
                          → ¬ (a ∈ xs) → xs ≡ filter-is-not a xs
if-not-there-filter-equal a [] np = refl
if-not-there-filter-equal a (x ∷ xs) np with a == x
... | yes refl = ⊥-elim (np (here a xs))
... | no neq rewrite sym (if-not-there-filter-equal a xs λ p → np (there a x xs p)) = refl
