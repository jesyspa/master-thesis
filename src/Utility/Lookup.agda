module Utility.Lookup where

open import ThesisPrelude
open import Utility.Elem
open import Utility.ListLemmas

SearchList : ∀ {l} (A B : Set l) → Set l
SearchList A B = List (A × B)

data Index {l} {A B : Set l} : A → SearchList A B → Set l where
  here : ∀ a b xs → Index a ((a , b) ∷ xs)
  there : ∀ a x xs → Index a xs → Index a (x ∷ xs)

Index-to-∈ : ∀{l} {A B : Set l} (a : A) (xs : SearchList A B)
           → Index a xs → a ∈ map fst xs
Index-to-∈ a .((a , b) ∷ xs) (here .a b xs) = here a (map fst xs)
Index-to-∈ a .(x ∷ xs) (there .a x xs p) = there a (fst x) (map fst xs) (Index-to-∈ a xs p)

∈-to-Index-helper : ∀{l} {A B : Set l} (a : A) (xs : SearchList A B) (as : List A)
                  → as ≡ map fst xs → a ∈ as → Index a xs
∈-to-Index-helper a [] ._ () (here .a as)
∈-to-Index-helper ._ (x ∷ xs) ._ refl (here ._ ._) with x
... | a , b = here a b xs
∈-to-Index-helper a [] ._ () (there .a y as p)
∈-to-Index-helper a (x ∷ xs) ._ refl (there .a ._ ._ p)
  = there a x xs (∈-to-Index-helper a xs (map fst xs) refl p)

∈-to-Index : ∀{l} {A B : Set l} (a : A) (xs : SearchList A B)
           → a ∈ map fst xs → Index a xs
∈-to-Index a xs p = ∈-to-Index-helper a xs (map fst xs) refl p

