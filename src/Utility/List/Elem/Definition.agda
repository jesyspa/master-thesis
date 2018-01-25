module Utility.List.Elem.Definition {l} {A : Set l} where

open import ThesisPrelude
open import Utility.List.Props
open import Algebra.Function

infix 4 _∈_
data _∈_ : A → List A → Set where
  here : ∀ x xs → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)

there-Inj : ∀{x y : A} {xs : List A} → Injective (there x y xs)
there-Inj refl = refl
  
neq-there : ∀(a x : A) (_ : ¬ (a ≡ x)) (xs : List A)
          → a ∈ x ∷ xs → a ∈ xs
neq-there a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
neq-there a x neq xs (there .a .x .xs p) = p

neq-there-lem : ∀(a x : A) (neq : ¬ (a ≡ x)) (xs : List A)
          → (p : a ∈ x ∷ xs)
          → p ≡ there a x xs (neq-there a x neq xs p)
neq-there-lem a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
neq-there-lem a x neq xs (there .a .x .xs p) = refl
