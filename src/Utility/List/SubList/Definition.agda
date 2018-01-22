module Utility.List.SubList.Definition {l} {A : Set l} where

open import ThesisPrelude

data SubList : List A → List A → Set where
  Empty : ∀ xs → SubList [] xs
  Keep : ∀ x xs ys → SubList xs ys → SubList (x ∷ xs) (y ∷ ys)
  Drop : ∀ x xs ys → SubList xs ys → SubList xs (y ∷ ys)
