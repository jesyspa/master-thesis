import ThesisPrelude as TP
module Utility.List.UniqueProps {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Utility.List.Props
open import Utility.List.Elem
open import Utility.List.Functions
open import Algebra.Function
open import Algebra.Equality
open import Algebra.ExactSize

unique-preserves-elem : (a : A) (xs : List A)
                      → a ∈ xs → a ∈ uniques xs
unique-preserves-elem a ._ (here .a xs) = here a $ filter (isNo ∘ (_==_ a)) (uniques xs)
unique-preserves-elem a ._ (there .a x xs p) with a == x
... | yes refl = here a (filter (isNo ∘ (_==_ a)) (uniques xs))
... | no neq = there a x (filter (isNo ∘ (_==_ x)) (uniques xs))
                         (filter-not-eq-preserves-elem a x (uniques xs) (neq ∘ sym)
                                                       (unique-preserves-elem a xs p))
                         
unique-preserves-elem-inv : (a : A) (xs : List A)
                          → a ∈ uniques xs → a ∈ xs
unique-preserves-elem-inv a [] ()
unique-preserves-elem-inv a (.a ∷ xs) (here .a ._) = here a xs
unique-preserves-elem-inv a (x ∷ xs) (there .a .x ._ p) with x == a
... | yes refl = ⊥-elim (not-in-filter-no a xs (filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ x)) p)) 
... | no neq = there a x xs (unique-preserves-elem-inv a xs (filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) p))

uniques-unique : (a : A) (xs : List A) (p : a ∈ xs)
               → (q : a ∈ uniques xs) → q ≡ unique-preserves-elem a xs p
uniques-unique a .(a ∷ xs) (here .a xs) (here .a ._) = refl
uniques-unique a .(a ∷ xs) (here .a xs) (there .a .a ._ q)
  = ⊥-elim (not-in-filter-no a xs (filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ a)) q))
uniques-unique a .(a ∷ xs) (there .a .a xs p) (here .a ._) with a == a
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)
uniques-unique a .(x ∷ xs) (there .a x xs p) (there .a .x ._ q) with x == a | a == x
... | yes refl | yes refl = ⊥-elim $ not-in-filter-no a xs $ filter-functional-inv a xs uniques (unique-preserves-elem-inv a xs) (isNo ∘ (_==_ a)) q
... | no neq   | yes refl = ⊥-elim $ neq refl
... | yes refl | no neq   = ⊥-elim $ neq refl
... | no neq   | no neq′  = cong (there a x (filter (isNo ∘ (_==_ x)) (uniques xs))) lem
  where
    lem2 : filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) q
         ≡ unique-preserves-elem a xs p
    lem2 = uniques-unique a xs p (filter-does-not-add-elements a (uniques xs) (isNo ∘ (_==_ x)) q) 
    lem : q ≡ filter-not-eq-preserves-elem a x (uniques xs) (neq′ ∘ sym) (unique-preserves-elem a xs p)
    lem = filter-does-not-add-elements-Inj a (uniques xs) (isNo ∘ (_==_ x))
            (lem2 ⟨≡⟩ filter-preserves-Ret a (uniques xs) (isNo ∘ (_==_ x)) (neq-is-no (neq′ ∘ sym)) (unique-preserves-elem a xs p) ) 

uniques-gives-singleton : (a : A) (xs : List A)
                        → a ∈ xs → [ a ] ≡ filter (isYes ∘ (_==_ a)) (uniques xs)
uniques-gives-singleton a xs p = singleton-elem a (uniques xs) (size1-lem (a ∈ uniques xs) (unique-preserves-elem a xs p) (uniques-unique a xs p)) 
