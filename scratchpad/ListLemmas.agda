module ListLemmas where

open import MyPrelude

right-append-lem : {A : Set} → {xs : List A} → xs ≡ xs ++ []
right-append-lem {A} {[]} = refl
right-append-lem {A} {x ∷ xs} = cong (_∷_ x) right-append-lem

map-id-lem : {A : Set} → {xs : List A} → map id xs ≡ xs
map-id-lem {A} {[]} = refl
map-id-lem {A} {x ∷ xs} = cong (_∷_ x) map-id-lem

map-weak-id-lem : {A : Set} → (f : A → A) → (xs : List A) → (∀{x} → x ≡ f x) → xs ≡ map f xs
map-weak-id-lem f [] p = refl
map-weak-id-lem f (x ∷ xs) p = cong₂ _∷_ p (map-weak-id-lem f xs p) 
