{-# OPTIONS --allow-unsolved-metas #-}
module ListLemmas where

open import MyPrelude

right-append-lem : {A : Set} → {xs : List A} → xs ≡ xs ++ []
right-append-lem {A} {[]} = refl
right-append-lem {A} {x ∷ xs} = cong (_∷_ x) right-append-lem

append-assoc-lem : {A : Set} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
append-assoc-lem [] ys zs = refl
append-assoc-lem (x ∷ xs) ys zs = cong (λ e →  x ∷ e) (append-assoc-lem xs ys zs)

map-id-lem : {A : Set} → (xs : List A) → xs ≡ map id xs
map-id-lem [] = refl
map-id-lem (x ∷ xs) = cong (_∷_ x) (map-id-lem xs)

map-equiv-lem : {A B : Set} → (f g : A → B) → (xs : List A) → ((x : A) → f x ≡ g x) → map f xs ≡ map g xs
map-equiv-lem f g [] p = refl
map-equiv-lem f g (x ∷ xs) p = cong₂ _∷_ (p x) (map-equiv-lem f g xs p) 

map-weak-id-lem : {A : Set} → (f : A → A) → (xs : List A) → ((x : A) → x ≡ f x) → xs ≡ map f xs
map-weak-id-lem f xs p = map-id-lem xs ⟨≡⟩ map-equiv-lem id f xs p

map-append-dist-lem : ∀{A B : Set}
                    → (f : A → B)
                    → (xs ys : List A)
                    → map f (xs ++ ys) ≡ map f xs ++ map f ys 
map-append-dist-lem f [] ys = refl
map-append-dist-lem f (x ∷ xs) ys = cong (λ e → f x ∷ e) (map-append-dist-lem f xs ys)

map-concatmap-swap-lem : ∀{A B C : Set}
                       → (f : B → C) → (g : A → List B) 
                       → (xs : List A)
                       → map f (concatMap g xs) ≡ concatMap (map f ∘ g) xs
map-concatmap-swap-lem f g [] = refl
map-concatmap-swap-lem f g (x ∷ xs) =
  map f (g x ++ concatMap g xs)
    ≡⟨ map-append-dist-lem f (g x) (concatMap g xs) ⟩
  map f (g x) ++ map f (concatMap g xs)
    ≡⟨ cong (λ e → map f (g x) ++ e) (map-concatmap-swap-lem f g xs) ⟩
  map f (g x) ++ concatMap (map f ∘ g) xs
  ∎

foldr-append-lem : ∀{A : Set}
                 → (f : A → A → A) → (e : A)
                 → (xs ys : List A)
                 → foldr f (foldr f e ys) xs ≡ foldr f e (xs ++ ys)
foldr-append-lem f e [] ys = refl
foldr-append-lem f e (x ∷ xs) ys = cong (f x) (foldr-append-lem f e xs ys)

map-compose-lem : ∀{A B C : Set}
                → (f : B → C) → (g : A → B)
                → (xs : List A)
                → map (f ∘ g) xs ≡ map f (map g xs)
map-compose-lem f g [] = refl
map-compose-lem f g (x ∷ xs) = cong (λ e → f (g x) ∷ e) (map-compose-lem f g xs)

