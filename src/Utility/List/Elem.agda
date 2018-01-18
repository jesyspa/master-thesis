module Utility.List.Elem where

open import ThesisPrelude
open import Utility.List.Props
open import Algebra.Equality
open import Algebra.Function
open import Algebra.ExactSize

infix 4 _∈_
data _∈_ {l} {A : Set l} : A → List A → Set l where
  here : ∀ x xs → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)
  
module _ {l} {A : Set l} where
  in-++-left : ∀ {a : A} (xs ys : List A)
             → a ∈ xs
             → a ∈ (xs ++ ys)
  in-++-left .(a ∷ xs) ys (here a xs) = here a (xs ++ ys)
  in-++-left .(y ∷ xs) ys (there a y xs p) = there a y (xs ++ ys) (in-++-left xs ys p)
  
  in-++-right : ∀ {a : A} (xs ys : List A)
              → a ∈ ys
              → a ∈ (xs ++ ys)
  in-++-right [] ys p = p
  in-++-right {a = a} (x ∷ xs) ys p = there a x (xs ++ ys) (in-++-right xs ys p)
  
  in-some-++ : ∀{a : A} (xs ys : List A)
             → a ∈ (xs ++ ys)
             → Either (a ∈ xs) (a ∈ ys)
  in-some-++ [] ys p = right p
  in-some-++ (a ∷ xs) ys (here .a .(xs ++ ys)) = left (here a xs)
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) with in-some-++ xs ys p
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | left pl = left (there a y xs pl)
  in-some-++ (y ∷ xs) ys (there a .y .(xs ++ ys) p) | right pr = right pr
  
  neq-there : ∀(a x : A) (_ : ¬ (a ≡ x)) (xs : List A)
            → a ∈ x ∷ xs → a ∈ xs
  neq-there a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
  neq-there a x neq xs (there .a .x .xs p) = p
  
  module _ {B : Set l} where
    map-preserves-in : ∀(f : A → B) (a : A) (xs : List A)
                     → a ∈ xs
                     → f a ∈ map f xs
    map-preserves-in f a .(a ∷ xs) (here .a xs) = here (f a) (map f xs)
    map-preserves-in f a .(x ∷ xs) (there .a x xs p) = there (f a) (f x) (map f xs) (map-preserves-in f a xs p)
    
    neq-there-lem : ∀(a x : A) (neq : ¬ (a ≡ x)) (xs : List A)
              → (p : a ∈ x ∷ xs)
              → p ≡ there a x xs (neq-there a x neq xs p)
    neq-there-lem a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
    neq-there-lem a x neq xs (there .a .x .xs p) = refl
    
    
    drop-map-lem-helper : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A) (ys : List B)
                        → ys ≡ map f xs → f a ∈ ys
                        → a ∈ xs
    drop-map-lem-helper f pf a [] .(f a ∷ ys) () (here .(f a) ys)
    drop-map-lem-helper f pf a (x ∷ xs) .(f a ∷ ys) eq (here .(f a) ys)
      rewrite pf (cons-inj-head eq) = here x xs
    drop-map-lem-helper f pf a [] .(y ∷ ys) () (there .(f a) y ys p)
    drop-map-lem-helper f pf a (x ∷ xs) .(y ∷ ys) eq (there .(f a) y ys p) = there a x xs (drop-map-lem-helper f pf a xs ys (cons-inj-tail eq) p)
    
    drop-map-lem : ∀(f : A → B) (_ : Injective f) (a : A) (xs : List A)
                 → f a ∈ map f xs
                 → a ∈ xs
    drop-map-lem f fp a xs p = drop-map-lem-helper f fp a xs (map f xs) refl p
    
  module _ {{_ : Eq A}} where
    equalFilter-fun : (a : A) (xs : List A)
                    → a ∈ xs → a ∈ filter (isYes ∘ (_==_ a)) xs
    equalFilter-fun a .(a ∷ xs) (here .a xs) rewrite yes-refl a = here a (filter (isYes ∘ (_==_ a)) xs)
    equalFilter-fun a .(y ∷ xs) (there .a y xs pf) with a == y
    equalFilter-fun a .(a ∷ xs) (there .a .a xs pf) | yes refl = there a a (filter (isYes ∘ (_==_ a)) xs) (equalFilter-fun a xs pf)
    equalFilter-fun a .(y ∷ xs) (there .a y xs pf) | no p = equalFilter-fun a xs pf
    
    equalFilter-inv : (a : A) (xs : List A)
                    → a ∈ filter (isYes ∘ (_==_ a)) xs → a ∈ xs
    equalFilter-inv a [] ()
    equalFilter-inv a (x ∷ xs) p with a == x
    equalFilter-inv a (.a ∷ xs) (here .a ._) | yes refl = here a xs
    equalFilter-inv a (.a ∷ xs) (there .a .a ._ p) | yes refl = there a a xs (equalFilter-inv a xs p)
    equalFilter-inv a (x ∷ xs) p | no pne = there a x xs (equalFilter-inv a xs p) 
