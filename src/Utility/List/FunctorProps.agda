module Utility.List.FunctorProps where

open import ThesisPrelude
open import Algebra.Function

map-ext : ∀{l l′} {A : Set l} {B : Set l′}
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

map-comp : ∀{l l′ l′′} {A : Set l} {B : Set l′} {C : Set l′′} (g : B → C) (f : A → B) (xs : List A)
         → map (g ∘′ f) xs ≡ map g (map f xs)
map-comp g f [] = refl
map-comp g f (x ∷ xs) rewrite sym (map-comp g f xs) = refl

module _ {l : Level} where
  open import Algebra.FunctorProps (List {l}) using (FunctorProps)
  instance
    FunctorPropsList : FunctorProps
    FunctorPropsList = record { fmap-ext = map-ext ; fmap-id = map-id ; fmap-comp = map-comp }

  map-ext-id : ∀{A : Set l} (f : A → A) → (∀ a → a ≡ f a) → (xs : List A)
             → xs ≡ map f xs
  map-ext-id = FunctorProps.fmap-ext-id FunctorPropsList
  
  map-lift-ret : ∀{A B : Set l} (g : B → A) (f : A → B)
               → Retraction g of f
               → Retraction map g of map f
  map-lift-ret = FunctorProps.fmap-lift-ret FunctorPropsList

map-const : ∀{l l′} {A : Set l} {B : Set l′} (b : B) (xs : List A)
          → replicate (length xs) b ≡ map (const b) xs
map-const b [] = refl
map-const b (x ∷ xs) rewrite sym (map-const b xs) = refl

map-replicate : ∀{l l′} {A : Set l} {B : Set l′} (n : Nat) (f : A → B) (a : A)
              → replicate n (f a) ≡ map f (replicate n a)
map-replicate zero f a = refl
map-replicate (suc n) f a rewrite sym (map-replicate n f a) = refl

map-length : ∀{l l′} {A : Set l} {B : Set l′} (f : A → B) (xs : List A)
           → length xs ≡ length (map f xs)
map-length f [] = refl
map-length f (x ∷ xs) rewrite sym (map-length f xs) = refl 
