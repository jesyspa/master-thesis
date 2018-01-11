module Utility.List.ComplexProps where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Function
open import Utility.List.MonoidProps

map-append-dist : ∀{l l′} {A : Set l} {B : Set l′}
                → (f : A → B)
                → (xs ys : List A)
                → map f (xs ++ ys) ≡ map f xs ++ map f ys 
map-append-dist f [] ys = refl
map-append-dist f (x ∷ xs) ys rewrite sym (map-append-dist f xs ys) = refl

filter-append-dist : ∀{l} {A : Set l}
                   → (p : A → Bool)
                   → (xs ys : List A)
                   → filter p (xs ++ ys) ≡ filter p xs ++ filter p ys 
filter-append-dist p [] ys = refl
filter-append-dist p (x ∷ xs) ys with p x
... | false = filter-append-dist p xs ys
... | true = cong (_∷_ x) (filter-append-dist p xs ys)

{-# DISPLAY foldr _++_ List.[] = concat #-}

concat-append-dist : ∀{l} {A : Set l}
                   → (xs ys : List (List A))
                   → concat (xs ++ ys) ≡ concat xs ++ concat ys 
concat-append-dist [] ys = refl
concat-append-dist (x ∷ xs) ys rewrite concat-append-dist xs ys = op-assoc x (concat xs) (concat ys)

concat-retraction : ∀{l} {A : Set l}
                  → Retraction concat {A = A} of map (λ x → x ∷ [])
concat-retraction [] = refl
concat-retraction (x ∷ xs) rewrite sym (concat-retraction xs) = refl

map-concatmap-swap : ∀{l} {A B C : Set l}
                   → (f : B → C) → (g : A → List B) 
                   → (xs : List A)
                   → map f (concatMap g xs) ≡ concatMap (map f ∘ g) xs
map-concatmap-swap f g [] = refl
map-concatmap-swap f g (x ∷ xs) rewrite sym (map-concatmap-swap f g xs) = map-append-dist f (g x) (concatMap g xs)

map-concat-swap : ∀{l} {A B : Set l}
                → (f : A → List (List B))
                → (xs : List A)
                → concat (map (concat ∘′ f) xs) ≡ concat (concat (map f xs))
map-concat-swap f [] = refl
map-concat-swap f (x ∷ xs) rewrite map-concat-swap f xs | concat-append-dist (f x) (concat (map f xs)) = refl

filter-reduction-identity : ∀{l} {A B : Set l} (g : B → A) (f : A → B) (p : A → Bool) (xs : List A)
                          → Retraction g of f
                          → map f (filter p xs) ≡ filter (p ∘ g) (map f xs)
filter-reduction-identity g f p [] pr = refl
filter-reduction-identity g f p (x ∷ xs) pr rewrite sym (pr x) with p x
... | false rewrite sym (filter-reduction-identity g f p xs pr) = refl
... | true rewrite sym (filter-reduction-identity g f p xs pr) = refl
