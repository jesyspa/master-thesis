module Utility.Elem where

open import ThesisPrelude
open import Algebra.Function

infix 4 _∈_
data _∈_ {l} {A : Set l} : A → List A → Set l where
  here : ∀ x xs → x ∈ (x ∷ xs)
  there : ∀ x y xs → x ∈ xs → x ∈ (y ∷ xs)

there-Inj : ∀{l} {A : Set l} (x y : A) (xs : List A)
          → Injective (there x y xs)
there-Inj x y xs a .a refl = refl

in-++-left : ∀ {l} {A : Set l} (x : A) (xs ys : List A)
           → x ∈ xs
           → x ∈ (xs ++ ys)
in-++-left x .(x ∷ xs) ys (here .x xs) = here x (xs ++ ys)
in-++-left x .(y ∷ xs) ys (there .x y xs p) = there x y (xs ++ ys) (in-++-left x xs ys p)

in-++-left-Inj : ∀{l} {A : Set l} (a : A) (xs ys : List A)
               → Injective (in-++-left a xs ys)
in-++-left-Inj a [] ys () ()
in-++-left-Inj a (.a ∷ xs) ys (here .a .xs) (here .a .xs) pe = refl
in-++-left-Inj a (.a ∷ xs) ys (here .a .xs) (there .a .a .xs pb) ()
in-++-left-Inj a (.a ∷ xs) ys (there .a .a .xs pa) (here .a .xs) ()
in-++-left-Inj a (x ∷ xs) ys (there .a .x .xs pa) (there .a .x .xs pb) pe
  rewrite in-++-left-Inj a xs ys pa pb (there-Inj a x (xs ++ ys) (in-++-left a xs ys pa) (in-++-left a xs ys pb) pe) = refl

in-++-right : ∀ {l} {A : Set l} (y : A) (xs ys : List A)
            → y ∈ ys
            → y ∈ (xs ++ ys)
in-++-right y [] ys p = p
in-++-right y (x ∷ xs) ys p = there y x (xs ++ ys) (in-++-right y xs ys p)

in-some-++ : ∀{l} {A : Set l} (x : A) (xs ys : List A)
           → x ∈ (xs ++ ys)
           → Either (x ∈ xs) (x ∈ ys)
in-some-++ x [] ys p = right p
in-some-++ x (.x ∷ xs) ys (here .x .(xs ++ ys)) = left (here x xs)
in-some-++ x (y ∷ xs) ys (there .x .y .(xs ++ ys) p) with in-some-++ x xs ys p
in-some-++ x (y ∷ xs) ys (there .x .y .(xs ++ ys) p) | left pl = left (there x y xs pl)
in-some-++ x (y ∷ xs) ys (there .x .y .(xs ++ ys) p) | right pr = right pr

map-preserves-in : ∀ {l} {A B : Set l} (x : A) (xs : List A) (f : A → B)
                 → x ∈ xs
                 → f x ∈ map f xs
map-preserves-in x .(x ∷ xs) f (here .x xs) = here (f x) (map f xs)
map-preserves-in x .(y ∷ xs) f (there .x y xs p) = there (f x) (f y) (map f xs) (map-preserves-in x xs f p)

equalFilter-fun : ∀{l} {A : Set l} {{_ : Eq A}}
                → (a : A) (xs : List A)
                → a ∈ xs → a ∈ filter (isYes ∘ (_==_ a)) xs
equalFilter-fun a .(a ∷ xs) (here .a xs) with a == a
equalFilter-fun a .(a ∷ xs) (here .a xs) | yes refl = here a (filter (isYes ∘ (_==_ a)) xs)
equalFilter-fun a .(a ∷ xs) (here .a xs) | no p = ⊥-elim (p refl)
equalFilter-fun a .(y ∷ xs) (there .a y xs pf) with a == y
equalFilter-fun a .(a ∷ xs) (there .a .a xs pf) | yes refl = there a a (filter (isYes ∘ (_==_ a)) xs) (equalFilter-fun a xs pf)
equalFilter-fun a .(y ∷ xs) (there .a y xs pf) | no p = equalFilter-fun a xs pf

{-
equalFilter-inj-helper : ∀{l} {A : Set l} {{_ : Eq A}}
                       → (a x : A) (xs : List A)
                       → Injective (equalFilter-fun a xs)
equalFilter-inj-helper  = ?

equalFilter-fun-red : ∀{l} {A : Set l} {{_ : Eq A}}
                    → (a x : A) (xs : List A)
                    → (p q : a ∈ xs)
                    → equalFilter-fun a (x ∷ xs) (there a x xs p) ≡ equalFilter-fun a (x ∷ xs) (there a x xs q)
                    → equalFilter-fun a xs p ≡ equalFilter-fun a xs q
equalFilter-fun-red a x xs p q pe with a == x
equalFilter-fun-red a .a xs p q pe | yes refl = {!!}
equalFilter-fun-red a x xs p q pe | no pr = {!!}


equalFilter-inj : ∀{l} {A : Set l} {{_ : Eq A}}
                → (a : A) (xs : List A)
                → Injective (equalFilter-fun a xs)
equalFilter-inj a .(a ∷ xs) (here .a xs) (here .a .xs) pe = refl
equalFilter-inj a .(a ∷ xs) (here .a xs) (there .a .a .xs q) pe = {!!}
equalFilter-inj a .(a ∷ xs) (there .a .a xs p) (here .a .xs) pe = {!!}
equalFilter-inj a .(y ∷ xs) (there .a y xs p) (there .a .y .xs q) = {!!}
-}

equalFilter-inv : ∀{l} {A : Set l} {{_ : Eq A}}
                → (a : A) (xs : List A)
                → a ∈ filter (isYes ∘ (_==_ a)) xs → a ∈ xs
equalFilter-inv a [] ()
equalFilter-inv a (x ∷ xs) p with a == x
equalFilter-inv a (.a ∷ xs) (here .a ._) | yes refl = here a xs
equalFilter-inv a (.a ∷ xs) (there .a .a ._ p) | yes refl = there a a xs (equalFilter-inv a xs p)
equalFilter-inv a (x ∷ xs) p | no pne = there a x xs (equalFilter-inv a xs p) 

{-
equalFilter-inv-sec : ∀{l} {A : Set l} {{_ : Eq A}}
                    → (a : A) (xs : List A)
                    → Section equalFilter-inv a xs of equalFilter-fun a xs
equalFilter-inv-sec a [] ()
equalFilter-inv-sec a (x ∷ xs) p with a == x
-}

postulate
  equalFilter-sec : ∀{l} {A : Set l} {{_ : Eq A}}
                  → (a : A) (xs : List A)
                  → Section equalFilter-fun a xs of equalFilter-inv a xs
  equalFilter-ret : ∀{l} {A : Set l} {{_ : Eq A}}
                  → (a : A) (xs : List A)
                  → Retraction equalFilter-fun a xs of equalFilter-inv a xs

equalFilter-lem : ∀{l} {A : Set l} {{_ : Eq A}}
                → (a : A) (xs : List A)
                → a ∈ xs ↔ a ∈ filter (isYes ∘ (_==_ a)) xs
equalFilter-lem a xs = equalFilter-fun a xs , equalFilter-inv a xs , equalFilter-sec a xs , equalFilter-ret a xs

