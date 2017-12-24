module Utility.Permutation where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Elem

module _ {l} {A : Set l} where
  Elements : List A → Set l
  Elements xs = Σ A λ x → x ∈ xs

  Permutation : List A → Set l
  Permutation xs = Σ (List A) λ ys → Elements xs ↔ Elements ys

  get-perm : ∀{xs : List A} (φ : Permutation xs) → List A
  get-perm = fst

  PermInvariant : ∀{r : Set l} (cmb : List A → r) → Set l
  PermInvariant cmb = ∀(xs : List A) (φ : Permutation xs) → cmb xs ≡ cmb (get-perm φ)

