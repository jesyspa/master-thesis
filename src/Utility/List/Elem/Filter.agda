import ThesisPrelude as TP
module Utility.List.Elem.Filter {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Utility.List.Elem.Definition
open import Algebra.Function
open import Algebra.ExactSize
open import Algebra.Equality

equalFilter-fun : (a : A) (xs : List A)
                → a ∈ xs → a ∈ filter (isYes ∘ (_==_ a)) xs
equalFilter-fun a .(a ∷ xs) (here .a xs) rewrite yes-refl a = here a (filter (isYes ∘ (_==_ a)) xs)
equalFilter-fun a .(y ∷ xs) (there .a y xs pf) with a == y
equalFilter-fun a .(a ∷ xs) (there .a .a xs pf) | yes refl = there a a (filter (isYes ∘ (_==_ a)) xs) (equalFilter-fun a xs pf)
equalFilter-fun a .(y ∷ xs) (there .a y xs pf) | no p = equalFilter-fun a xs pf

equalFilter-inv : (a : A) (xs : List A)
                → a ∈ filter (isYes ∘ (_==_ a)) xs → a ∈ xs
equalFilter-inv a [] ()
equalFilter-inv a (x ∷ xs) p with a == x
equalFilter-inv a (.a ∷ xs) (here .a ._) | yes refl = here a xs
equalFilter-inv a (.a ∷ xs) (there .a .a ._ p) | yes refl = there a a xs (equalFilter-inv a xs p)
equalFilter-inv a (x ∷ xs) p | no pne = there a x xs (equalFilter-inv a xs p) 

filter-does-not-add-elements : (a : A) (xs : List A) (pd : A → Bool)
                             → a ∈ filter pd xs → a ∈ xs
filter-does-not-add-elements a [] pd ()
filter-does-not-add-elements a (x ∷ xs) pd p with pd x
filter-does-not-add-elements .x (x ∷ xs) pd (here .x ._)      | true = here x xs
filter-does-not-add-elements a (x ∷ xs) pd (there .a .x ._ p) | true = there a x xs (filter-does-not-add-elements a xs pd p)
... | false = there a x xs (filter-does-not-add-elements a xs pd p)

filter-preserves-satisfying : (a : A) (xs : List A) (pd : A → Bool)
                            → IsTrue (pd a)
                            → a ∈ xs → a ∈ filter pd xs
filter-preserves-satisfying a .(a ∷ xs) pd pf (here .a xs) with pd a
... | true = here a (filter pd xs)
filter-preserves-satisfying a .(a ∷ xs) pd () (here .a xs) | false
filter-preserves-satisfying a .(y ∷ xs) pd pf (there .a y xs p) with pd y
... | true = there a y (filter pd xs) (filter-preserves-satisfying a xs pd pf p)
... | false = filter-preserves-satisfying a xs pd pf p

filter-not-eq-preserves-elem : (a x : A) (xs : List A)
                             → ¬ (x ≡ a) → a ∈ xs → a ∈ filter (isNo ∘ (_==_ x)) xs
filter-not-eq-preserves-elem a x xs neq = filter-preserves-satisfying a xs (isNo ∘ (_==_ x)) (neq-is-no neq)

filter-removes-unsatisfying : (a : A) (xs : List A) (pd : A → Bool)
                            → IsFalse (pd a)
                            → ¬ (a ∈ filter pd xs)
filter-removes-unsatisfying a [] pd pf ()
filter-removes-unsatisfying a (x ∷ xs) pd pf p with pd x | graphAt pd x
filter-removes-unsatisfying .x (x ∷ xs) pd pf (here .x ._) | true | ingraph pig rewrite pig with pf
... | ()
filter-removes-unsatisfying a (x ∷ xs) pd pf (there .a .x ._ p) | true | ingraph pig = filter-removes-unsatisfying a xs pd pf p
filter-removes-unsatisfying a (x ∷ xs) pd pf p | false | ingraph pig = filter-removes-unsatisfying a xs pd pf p

filter-functional-inv : (a : A) (xs : List A) (f : List A → List A) (fp : a ∈ f xs → a ∈ xs)
                              → (pd : A → Bool)
                              → a ∈ filter pd (f xs) → a ∈ filter pd xs
filter-functional-inv a xs f fp pd p with pd a | graphAt pd a
... | true | ingraph pig = filter-preserves-satisfying a xs pd (transport IsTrue (sym pig) it)
                                                       (fp (filter-does-not-add-elements a (f xs) pd p))
... | false | ingraph pig = ⊥-elim (filter-removes-unsatisfying a (f xs) pd (transport IsFalse (sym pig) it) p)

not-in-filter-no : (a : A) (xs : List A)
                 → ¬ (a ∈ filter (isNo ∘ (_==_ a)) xs)
not-in-filter-no a [] ()
not-in-filter-no a (x ∷ xs) p with a == x
... | yes refl = not-in-filter-no a xs p
not-in-filter-no a (.a ∷ xs) (here .a ._) | no neq = neq refl
not-in-filter-no a (x ∷ xs) (there .a .x ._ p) | no neq = not-in-filter-no a xs p
