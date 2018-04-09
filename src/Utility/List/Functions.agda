module Utility.List.Functions where

open import ThesisPrelude
open import Utility.List.Elem.Decidable

uniques : ∀{l} {A : Set l} {{_ : Eq A}} → List A → List A
uniques [] = []
uniques (x ∷ xs) with decide-elem x xs
... | yes _ = uniques xs
... | no _  = x ∷ uniques xs

disjoint-union : ∀{l} {A : Set l} {{_ : Eq A}} → List A → List A → List A
disjoint-union xs ys = uniques (xs ++ ys)
