module Utility.List.Props.Monoid where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Function

list-++-assoc : ∀{l} {A : Set l} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs 
list-++-assoc [] ys zs = refl
list-++-assoc (x ∷ xs) ys zs rewrite list-++-assoc xs ys zs = refl

list-++-right-identity : ∀{l} {A : Set l} → (xs : List A) → xs ≡ xs ++ []
list-++-right-identity [] = refl
list-++-right-identity (x ∷ xs) rewrite sym (list-++-right-identity xs) = refl

instance
  MonoidPropsList : ∀{l} {A : Set l} → MonoidProps (List A)
  MonoidPropsList = record { op-assoc = list-++-assoc ; unit-left = λ a → refl ; unit-right = list-++-right-identity }
