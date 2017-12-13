module Utility.VecProps where

open import ThesisPrelude hiding (List)


infixr 5 _my∷_
_my∷_ : ∀{l} {A : Set l} {n} → (x : A) → (xs : Vec A n) → Vec A (suc n)
_my∷_ = _∷_

head-equality : ∀ {A : Set} {n : Nat} (x y : A) (xs ys : Vec A n)
              → x my∷ xs ≡ y my∷ ys
              → x ≡ y
head-equality x .x xs .xs refl = refl

tail-equality : ∀ {A : Set} {n : Nat} (x y : A) (xs ys : Vec A n)
              → x my∷ xs ≡ y my∷ ys
              → xs ≡ ys
tail-equality x .x xs .xs refl = refl

componentwise-equality : ∀ {A : Set} {n : Nat} (x y : A) (xs ys : Vec A n)
                       → Dec (x ≡ y) → Dec (xs ≡ ys)
                       → Dec (x my∷ xs ≡  y my∷ ys)
componentwise-equality x .x xs .xs (yes refl) (yes refl) = yes refl
componentwise-equality x y xs ys (no ph) _ = no λ p → ph (head-equality x y xs ys p)
componentwise-equality x y xs ys _ (no  pt) = no λ p → pt (tail-equality x y xs ys p)

vec-eq : ∀{A : Set} {{_ : Eq A}} {n} → (xs ys : Vec A n) → Dec (xs ≡ ys)
vec-eq [] [] = yes refl
vec-eq (x ∷ xs) (y ∷ ys) = {!!}


