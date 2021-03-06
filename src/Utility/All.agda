module Utility.All where

open import ThesisPrelude

infixr 5 _∷_
data All {l l′}{A : Set l}(P : A → Set l′) : List A → Set l′ where
  [] : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

All′ : ∀{l} → List (Set l) → Set l
All′ xs = All id xs

split-All : ∀{l l′}{A : Set l}{P : A → Set l′}(xs ys : List A)
          → All P (xs ++ ys)
          → All P xs × All P ys
split-All [] ys ps = [] , ps
split-All (x ∷ xs) ys (p ∷ ps) with split-All xs ys ps
... | rs , qs = p ∷ rs , qs
