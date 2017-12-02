module Elem where

open import MyPrelude

data _∈_ {A : Set} (x : A) : List A → Set where 
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

lookup : ∀{A P xs} → {x : A} → All P xs → x ∈ xs → P x
lookup (px ∷ axs) here = px
lookup (_ ∷ axs) (there p) = lookup axs p
