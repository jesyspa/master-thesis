module Utility.List.SubList.Definition {l} {A : Set l} where

open import ThesisPrelude

data SubList : List A → List A → Set where
  EmptySL : ∀ xs → SubList [] xs
  KeepSL : ∀ x {xs ys} → SubList xs ys → SubList (x ∷ xs) (x ∷ ys)
  DropSL : ∀ x {xs ys} → SubList xs ys → SubList xs (x ∷ ys)

_⊑_ : List A → List A → Set
xs ⊑ ys = SubList xs ys
