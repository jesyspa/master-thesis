module Utility.List.SubList.Definition {l} {A : Set l} where

open import ThesisPrelude

data SubList : List A → List A → Set where
  Empty : ∀ xs → SubList [] xs
  Keep : ∀ x {xs ys} → SubList xs ys → SubList (x ∷ xs) (x ∷ ys)
  Drop : ∀ x {xs ys} → SubList xs ys → SubList xs (x ∷ ys)

_⊑_ : List A → List A → Set
xs ⊑ ys = SubList xs ys

postulate
  refl-⊑ : ∀ xs → xs ⊑ xs
  cons-⊑ : ∀{x xs ys}→ (x ∷ xs) ⊑ ys → xs ⊑ ys
