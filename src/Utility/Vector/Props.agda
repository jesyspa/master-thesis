module Utility.Vector.Props where

open import ThesisPrelude hiding (List)

componentwise-equality : ∀ {A : Set} {n : Nat} (x y : A) (xs ys : Vec A n)
                       → Dec (x ≡ y) → Dec (xs ≡ ys)
                       → Dec (_≡_ {A = Vec A (suc n)} (x ∷ xs) (y ∷ ys))
componentwise-equality x .x xs .xs (yes refl) (yes refl) = yes refl
componentwise-equality x y xs ys (no ph) _ = no λ p → ph (vcons-inj-head p)
componentwise-equality x y xs ys _ (no  pt) = no λ p → pt (vcons-inj-tail p)

vec-eq : ∀{A : Set} {{_ : Eq A}} {n} → (xs ys : Vec A n) → Dec (xs ≡ ys)
vec-eq [] [] = yes refl
vec-eq (x ∷ xs) (y ∷ ys) = componentwise-equality x y xs ys (x == y) (xs == ys) 


