open import ThesisPrelude using (Ord)
module Algebra.Preorder (A : Set){{_ : Ord A}} where

open import ThesisPrelude

record PreorderProps : Set where
  field
    ≤-refl  : (a : A)                     → a ≤ a
    ≤-antisym : {a b : A} → a ≤ b → b ≤ a → a ≡ b
    ≤-trans : {a b c : A} → a ≤ b → b ≤ c → a ≤ c
    <-norefl : (a : A) → ¬ (a < a)
    <-trans : {a b c : A} → a < b → b < c → a < c

