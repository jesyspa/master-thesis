module Utility.List.Functions where

open import ThesisPrelude

uniques : ∀{l} {A : Set l} {{_ : Eq A}} → List A → List A
uniques [] = []
uniques (x ∷ xs) = x ∷ filter (isNo ∘ (_==_ x)) (uniques xs)

count : ∀{l}{A : Set l}{{_ : Eq A}} → List A → A → Nat
count [] a = 0
count (x ∷ xs) a with a == x
... | yes _ = 1 + count xs a
... | no  _ = count xs a
