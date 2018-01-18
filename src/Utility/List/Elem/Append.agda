module Utility.List.Elem.Append {l} {A : Set l} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition

in-++-left : ∀ {a : A} (xs ys : List A)
           → a ∈ xs
           → a ∈ (xs ++ ys)
in-++-left .(a ∷ xs) ys (here a xs) = here a (xs ++ ys)
in-++-left .(y ∷ xs) ys (there a y xs p) = there a y (xs ++ ys) (in-++-left xs ys p)

in-++-right : ∀ {a : A} (xs ys : List A)
            → a ∈ ys
            → a ∈ (xs ++ ys)
in-++-right [] ys p = p
in-++-right {a = a} (x ∷ xs) ys p = there a x (xs ++ ys) (in-++-right xs ys p)

in-some-++ : ∀{a : A} (xs ys : List A)
           → a ∈ (xs ++ ys)
           → Either (a ∈ xs) (a ∈ ys)
in-some-++ [] ys p = right p
in-some-++ (a ∷ xs) ys (here .a .(xs ++ ys)) = left (here a xs)
in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) with in-some-++ xs ys p
in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | left pl = left (there a y xs pl)
in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | right pr = right pr
