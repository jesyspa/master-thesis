module Utility.List.Elem.Map {l l′}{A : Set l}{B : Set l′} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition

map-preserves-in : ∀(f : A → B) (a : A) (xs : List A)
                 → a ∈ xs
                 → f a ∈ map f xs
map-preserves-in f a .(a ∷ xs) (here .a xs) = here (f a) (map f xs)
map-preserves-in f a .(x ∷ xs) (there .a x xs p) = there (f a) (f x) (map f xs) (map-preserves-in f a xs p)

drop-map-lem-helper : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A) (ys : List B)
                    → ys ≡ map f xs → f a ∈ ys
                    → a ∈ xs
drop-map-lem-helper f pf a [] .(f a ∷ ys) () (here .(f a) ys)
drop-map-lem-helper f pf a (x ∷ xs) .(f a ∷ ys) eq (here .(f a) ys)
  rewrite pf (cons-inj-head eq) = here x xs
drop-map-lem-helper f pf a [] .(y ∷ ys) () (there .(f a) y ys p)
drop-map-lem-helper f pf a (x ∷ xs) .(y ∷ ys) eq (there .(f a) y ys p) = there a x xs (drop-map-lem-helper f pf a xs ys (cons-inj-tail eq) p)

drop-map-lem : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A)
             → f a ∈ map f xs
             → a ∈ xs
drop-map-lem f fp a xs p = drop-map-lem-helper f fp a xs (map f xs) refl p
