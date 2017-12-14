{-# OPTIONS --allow-unsolved-metas #-}
module Utility.ListLemmas where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Functor

list-++-assoc : ∀{l} {A : Set l} → (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs 
list-++-assoc [] ys zs = refl
list-++-assoc (x ∷ xs) ys zs rewrite list-++-assoc xs ys zs = refl

list-++-right-identity : ∀{l} {A : Set l} → (xs : List A) → xs ≡ xs ++ []
list-++-right-identity [] = refl
list-++-right-identity (x ∷ xs) rewrite sym (list-++-right-identity xs) = refl

instance
  MonoidPropsList : ∀{l} {A : Set l} → MonoidProps (List A)
  MonoidPropsList = record { op-assoc = list-++-assoc ; unit-left = λ a → refl ; unit-right = list-++-right-identity }

map-ext : ∀{l} {A B : Set l}
        → (f g : A → B)
        → (∀ a → f a ≡ g a)
        → (xs : List A)
        → map f xs ≡ map g xs
map-ext f g p [] = refl
map-ext f g p (x ∷ xs) rewrite map-ext f g p xs | p x = refl

map-id : ∀{l} {A : Set l}
       → (xs : List A)
       → xs ≡ map id xs
map-id [] = refl
map-id (x ∷ xs) rewrite sym (map-id xs) = refl

map-comp : ∀{l} {A B C : Set l} (g : B → C) (f : A → B) (xs : List A)
         → fmap (g ∘′ f) xs ≡ fmap g (fmap f xs)
map-comp g f [] = refl
map-comp g f (x ∷ xs) rewrite map-comp g f xs = refl

map-append-dist : ∀{l} {A B : Set l}
                → (f : A → B)
                → (xs ys : List A)
                → map f (xs ++ ys) ≡ map f xs ++ map f ys 
map-append-dist f [] ys = refl
map-append-dist f (x ∷ xs) ys rewrite sym (map-append-dist f xs ys) = refl

map-concatmap-swap : ∀{l} {A B C : Set l}
                   → (f : B → C) → (g : A → List B) 
                   → (xs : List A)
                   → map f (concatMap g xs) ≡ concatMap (map f ∘ g) xs
map-concatmap-swap f g [] = refl
map-concatmap-swap f g (x ∷ xs) rewrite sym (map-concatmap-swap f g xs) = map-append-dist f (g x) (concatMap g xs)

list-<*>-composition : ∀{l} {A B C : Set l} (xs : List (B → C)) (ys : List (A → B)) (zs : List A)
                     → (xs <*> (ys <*> zs)) ≡ ([ _∘′_ ] <*> xs <*> ys <*> zs)
list-<*>-composition [] ys zs = refl
list-<*>-composition (x ∷ xs) ys zs rewrite sym (list-<*>-composition xs ys zs) =
  map x (concat (map (λ f → map f zs) ys)) ++ concat (map (λ f → map f (concat (map (λ g → map g zs) ys))) xs)

    ≡⟨ {!!} ⟩
  concat
    (map (λ z → map z zs)
     (map (λ z x₁ → x (z x₁)) ys ++
      concat
      (map (λ z → map z ys) (map (λ z x₁ x₂ → z (x₁ x₂)) xs ++ []))))
--  concat (map (λ f → map f zs) (map (_∘′_ x) ys ++ concat (map (λ f → map f zs) (map _∘′_ xs ++ []))))
  ∎
{-
  (x ∷ xs) <*> (ys <*> zs)
    ≡⟨ refl ⟩
  concatMap (λ f → map f (concatMap (λ g → map g zs) ys)) (x ∷ xs)
    ≡⟨ refl ⟩
  map x (concatMap (λ g → map g zs) ys) ++ concatMap (λ f → map f (concatMap (λ g → map g zs) ys)) xs
    ≡⟨ cong (λ e → map x (concatMap (λ g → map g zs) ys) ++ e) (list-<*>-composition xs ys zs) ⟩
  map x (concatMap (λ g → map g zs) ys) ++ concatMap (λ f → map f (concatMap (λ g → map g zs) ys)) xs
    ≡⟨ {!!} ⟩
  concat (concatMap (map (λ f → map f zs) ∘′ ((λ g → map g ys) ∘′ _∘′_)) (x ∷ xs))
    ≡⟨ cong concat (sym (map-concatmap-swap (λ z → map z zs) (λ z → map (_∘′_ z) ys) (x ∷ xs))) ⟩
  concatMap (λ f → map f zs) (concatMap ((λ g → map g ys) ∘′ _∘′_) (x ∷ xs))
    ≡⟨ cong (λ e → concatMap (λ f → map f zs) (concat e)) (map-comp (λ g → map g ys) _∘′_ (x ∷ xs)) ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (map _∘′_ (x ∷ xs)))
    ≡⟨ cong (λ e → concatMap (λ f → map f zs) (concatMap (λ g → map g ys) e)) (unit-right (map _∘′_ (x ∷ xs))) ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (map _∘′_ (x ∷ xs) ++ []))
    ≡⟨ refl ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (concatMap (λ h → map h (x ∷ xs)) [ _∘′_ ]))
    ≡⟨ refl ⟩
  [ _∘′_ ] <*> (x ∷ xs) <*> ys <*> zs
  ∎
  -}
{-
  xs <*> (ys <*> zs)
    ≡⟨ refl ⟩
  concatMap (λ f → map f (concatMap (λ g → map g zs) ys)) xs
    ≡⟨ {!!} ⟩
  concatMap (λ f → {!!}) xs
    ≡⟨ {!!} ⟩
  concat (concatMap (λ a → map (λ f → map f zs) (map (_∘′_ a) ys)) xs)
    ≡⟨ refl ⟩
  concat (concatMap (λ a → map (λ f → map f zs) (((λ g → map g ys) ∘′ _∘′_) a)) xs)
    ≡⟨ refl ⟩
  concat (concatMap (λ a → (map (λ f → map f zs) ∘′ ((λ g → map g ys) ∘′ _∘′_)) a) xs)
    ≡⟨ refl ⟩
  concat (concatMap (map (λ f → map f zs) ∘′ ((λ g → map g ys) ∘′ _∘′_)) xs)
    ≡⟨ cong concat (sym (map-concatmap-swap (λ z → map z zs) (λ z → map (_∘′_ z) ys) xs)) ⟩
  concatMap (λ f → map f zs) (concatMap ((λ g → map g ys) ∘′ _∘′_) xs)
    ≡⟨ cong (λ e → concatMap (λ f → map f zs) (concat e)) (map-comp (λ g → map g ys) _∘′_ xs) ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (map _∘′_ xs))
    ≡⟨ cong (λ e → concatMap (λ f → map f zs) (concatMap (λ g → map g ys) e)) (unit-right (map _∘′_ xs)) ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (map _∘′_ xs ++ []))
    ≡⟨ refl ⟩
  concatMap (λ f → map f zs) (concatMap (λ g → map g ys) (concatMap (λ h → map h xs) [ _∘′_ ]))
    ≡⟨ refl ⟩
  [ _∘′_ ] <*> xs <*> ys <*> zs
  ∎
  -}
list-<*>-homomorphism : ∀{l} {A B : Set l} (f : A → B) (x : A)
                      → [ f x ] ≡ ([ f ] <*> [ x ])
list-<*>-homomorphism  = {!!}
list-<*>-interchange : ∀{l} {A B : Set l} (xs : List (A → B)) (y : A)
                     → (xs <*> [ y ]) ≡ ([ (λ f → f y) ] <*> xs)
list-<*>-interchange  = {!!}
list-fmap-is-pure-<*> : ∀{l} {A B : Set l} (f : A → B) (xs : List A)
                      → fmap f xs ≡ ([ f ] <*> xs)
list-fmap-is-pure-<*>  = {!!}

instance
  FunctorPropsList : ∀{l} → FunctorProps {l} List
  FunctorPropsList = record { fmap-ext = map-ext ; fmap-id = map-id ; fmap-comp = map-comp }
