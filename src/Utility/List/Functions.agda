module Utility.List.Functions where

open import ThesisPrelude

uniques : ∀{l} {A : Set l} {{_ : Eq A}} → List A → List A
uniques [] = []
uniques (x ∷ xs) = x ∷ filter (isNo ∘ (_==_ x)) (uniques xs)
