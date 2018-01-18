module Utility.List.Lookup.Elem {l}{A B : Set l} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Product
open import Utility.List.Elem
open import Utility.List.Props
open import Utility.List.Lookup.Definition

Index-to-∈ : ∀(a : A) (xs : SearchList A B)
           → Index a xs → a ∈ map fst xs
Index-to-∈ a .((a , b) ∷ xs) (here .a b xs) = here a (map fst xs)
Index-to-∈ a .(x ∷ xs) (there .a x xs p) = there a (fst x) (map fst xs) (Index-to-∈ a xs p)

Index-to-∈′ : ∀(a : A) (xs : List A) (f : A → A × B)
            → ((x : A) → x ≡ fst (f x))
            → Index a (map f xs) → a ∈ xs 
Index-to-∈′ a xs f eq p = transport (_∈_ a) (sym $ map-lift-ret fst f eq xs) (Index-to-∈ a (map f xs) p)

∈-to-Index-helper : ∀ (a : A) (xs : SearchList A B) (as : List A)
                  → as ≡ map fst xs → a ∈ as → Index a xs
∈-to-Index-helper a [] ._ () (here .a as)
∈-to-Index-helper ._ (x ∷ xs) ._ refl (here ._ ._) with x
... | a , b = here a b xs
∈-to-Index-helper a [] ._ () (there .a y as p)
∈-to-Index-helper a (x ∷ xs) ._ refl (there .a ._ ._ p)
  = there a x xs (∈-to-Index-helper a xs (map fst xs) refl p)

∈-to-Index : ∀ (a : A) (xs : SearchList A B)
           → a ∈ map fst xs → Index a xs
∈-to-Index a xs p = ∈-to-Index-helper a xs (map fst xs) refl p

∈-to-Index′ : ∀(a : A) (xs : List A) (f : A → A × B)
            → ((x : A) → x ≡ fst (f x))
            → a ∈ xs → Index a (map f xs)
∈-to-Index′ a xs f eq p = ∈-to-Index a (map f xs) (transport (_∈_ a) (map-lift-ret fst f eq xs) p)

∈-to-annotate-Index : ∀(a : A) (xs : List A) (b : B)
                    → a ∈ xs → Index a (annotate b xs)
∈-to-annotate-Index a xs b p = ∈-to-Index′ a xs (rev-pair b) (λ x → refl) p

annotate-Index-to-∈ : ∀(a : A) (xs : List A) (b : B)
                    → Index a (annotate b xs) → a ∈ xs
annotate-Index-to-∈ a xs b p = Index-to-∈′ a xs (rev-pair b) (λ x → refl) p
