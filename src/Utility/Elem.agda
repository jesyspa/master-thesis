module Utility.Elem where

open import ThesisPrelude

infix 20 _∈_
data _∈_ {l} {A : Set l} : A → List A → Set l where
  here : ∀ x xs → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)

in-++-left : ∀ {l} {A : Set l} (x : A) (xs ys : List A)
           → x ∈ xs
           → x ∈ (xs ++ ys)
in-++-left x .(x ∷ xs) ys (here .x xs) = here x (xs ++ ys)
in-++-left x .(y ∷ xs) ys (there .x y xs p) = there x y (xs ++ ys) (in-++-left x xs ys p)

in-++-right : ∀ {l} {A : Set l} (y : A) (xs ys : List A)
            → y ∈ ys
            → y ∈ (xs ++ ys)
in-++-right y [] ys p = p
in-++-right y (x ∷ xs) ys p = there y x (xs ++ ys) (in-++-right y xs ys p)

map-preserves-in : ∀ {l} {A B : Set l} (x : A) (xs : List A) (f : A → B)
                 → x ∈ xs
                 → f x ∈ map f xs
map-preserves-in x .(x ∷ xs) f (here .x xs) = here (f x) (map f xs)
map-preserves-in x .(y ∷ xs) f (there .x y xs p) = there (f x) (f y) (map f xs) (map-preserves-in x xs f p)
