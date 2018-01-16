module Utility.Vector.Functions where

open import ThesisPrelude

vall : ∀{n} → Vec Bool n → Bool
vall = vfoldr _&&_ true

vzip : ∀{l} {A B : Set l} {n} → (A → A → B) → (xs ys : Vec A n) → Vec B n
vzip f [] [] = []
vzip f (x ∷ xs) (y ∷ ys) = f x y ∷ vzip f xs ys

head : ∀{l} {A : Set l} {n} → Vec A (suc n) → A
head (x ∷ _) = x

head1 : ∀{l} {A : Set l} → Vec A 1 → A
head1 = head {n = zero}
