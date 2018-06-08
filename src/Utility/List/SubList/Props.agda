module Utility.List.SubList.Props {l} {A : Set l} where

open import ThesisPrelude
open import Utility.List.SubList.Definition {A = A}

refl-⊑ : ∀ xs → xs ⊑ xs
refl-⊑ [] = EmptySL []
refl-⊑ (x ∷ xs) = KeepSL x (refl-⊑ xs)

cons-⊑ : ∀{x xs ys} → (x ∷ xs) ⊑ ys → xs ⊑ ys
cons-⊑ (KeepSL x sub) = DropSL x sub
cons-⊑ (DropSL x sub) = DropSL x (cons-⊑ sub)
