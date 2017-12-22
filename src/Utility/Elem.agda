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

in-++-right : ∀ {l} {A : Set l} (a : A) (xs ys : List A)
            → a ∈ ys
            → a ∈ (xs ++ ys)
in-++-right a [] ys p = p
in-++-right a (x ∷ xs) ys p = there a x (xs ++ ys) (in-++-right a xs ys p)

in-some-++ : ∀{l} {A : Set l} (a : A) (xs ys : List A)
           → a ∈ (xs ++ ys)
           → Either (a ∈ xs) (a ∈ ys)
in-some-++ a [] ys p = right p
in-some-++ a (.a ∷ xs) ys (here .a .(xs ++ ys)) = left (here a xs)
in-some-++ a (y ∷ xs) ys (there .a .y .(xs ++ ys) p) with in-some-++ a xs ys p
in-some-++ a (y ∷ xs) ys (there .a .y .(xs ++ ys) p) | left pl = left (there a y xs pl)
in-some-++ a (y ∷ xs) ys (there .a .y .(xs ++ ys) p) | right pr = right pr

in-some-++-left : ∀{l} {A : Set l} (a : A) (xs ys : List A)
                → (p : a ∈ xs)
                → left p ≡ in-some-++ a xs ys (in-++-left a xs ys p)
in-some-++-left a [] ys ()
in-some-++-left a (.a ∷ xs) ys (here .a .xs) = refl
in-some-++-left a (x ∷ xs) ys (there .a .x .xs p)
  rewrite sym (in-some-++-left a xs ys p) = refl

in-some-++-right : ∀{l} {A : Set l} (a : A) (xs ys : List A)
                → (p : a ∈ ys)
                → right p ≡ in-some-++ a xs ys (in-++-right a xs ys p)
in-some-++-right a [] ys p = refl
in-some-++-right a (x ∷ xs) ys p rewrite sym (in-some-++-right a xs ys p) = refl

in-some-++-Inj : ∀{l} {A : Set l} (a : A) (xs ys : List A)
               → Injective (in-some-++ a xs ys)
in-some-++-Inj a [] ys p .p refl = refl
in-some-++-Inj a (.a ∷ xs) ys (here .a ._) (here .a ._) pe = refl
in-some-++-Inj a (.a ∷ xs) ys (here .a ._) (there .a .a ._ q) pe with in-some-++ a xs ys q
in-some-++-Inj a (.a ∷ xs) ys (here .a ._) (there .a .a ._ q) () | left _
in-some-++-Inj a (.a ∷ xs) ys (here .a ._) (there .a .a ._ q) () | right _
in-some-++-Inj a (.a ∷ xs) ys (there .a .a ._ p) (here .a ._) pe with in-some-++ a xs ys p
in-some-++-Inj a (.a ∷ xs) ys (there .a .a ._ p) (here .a ._) () | left _
in-some-++-Inj a (.a ∷ xs) ys (there .a .a ._ p) (here .a ._) () | right _
in-some-++-Inj a (x ∷ xs) ys (there .a .x ._ p) (there .a .x ._ q) pe
  with in-some-++ a xs ys p | graphAt (in-some-++ a xs ys) p
     | in-some-++ a xs ys q | graphAt (in-some-++ a xs ys) q
in-some-++-Inj a (x ∷ xs) ys (there .a .x ._ p) (there .a .x ._ q) refl
     | left pl | ingraph pig
     | left .pl | ingraph qig
     rewrite in-some-++-Inj a xs ys p q (pig ⟨≡⟩ʳ qig) = refl
in-some-++-Inj a (x ∷ xs) ys (there .a .x ._ p) (there .a .x ._ q) () | left pl | ingraph pig | right qr | ingraph qig
in-some-++-Inj a (x ∷ xs) ys (there .a .x ._ p) (there .a .x ._ q) () | right pl | ingraph pig | left qr | ingraph qig
in-some-++-Inj a (x ∷ xs) ys (there .a .x ._ p) (there .a .x ._ q) refl
     | right pl | ingraph pig
     | right .pl | ingraph qig
     rewrite in-some-++-Inj a xs ys p q (pig ⟨≡⟩ʳ qig) = refl

map-preserves-in : ∀ {l} {A B : Set l} (f : A → B) (a : A) (xs : List A)
                 → a ∈ xs
                 → f a ∈ map f xs
map-preserves-in f a .(a ∷ xs) (here .a xs) = here (f a) (map f xs)
map-preserves-in f a .(x ∷ xs) (there .a x xs p) = there (f a) (f x) (map f xs) (map-preserves-in f a xs p)

neq-there : ∀{l} {A : Set l} (a x : A) (_ : ¬ (a ≡ x)) (xs : List A)
          → a ∈ x ∷ xs → a ∈ xs
neq-there a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
neq-there a x neq xs (there .a .x .xs p) = p

neq-there-lem : ∀{l} {A : Set l} (a x : A) (neq : ¬ (a ≡ x)) (xs : List A)
          → (p : a ∈ x ∷ xs)
          → p ≡ there a x xs (neq-there a x neq xs p)
neq-there-lem a .a neq xs (here .a .xs) = ⊥-elim (neq refl)
neq-there-lem a x neq xs (there .a .x .xs p) = refl

-- The Eq A assumption is kind of weird
drop-map-lem : ∀{l} {A B : Set l} {{_ : Eq A}} (f : A → B) (_ : Injective f) (a : A) (xs : List A)
             → f a ∈ map f xs
             → a ∈ xs
drop-map-lem f fp a [] ()
drop-map-lem f fp a (x ∷ xs) p with a == x
drop-map-lem f fp a (.a ∷ xs) (here .(f a) .(map f xs)) | yes refl = here a xs
drop-map-lem f fp a (.a ∷ xs) (there .(f a) .(f a) .(map f xs) p) | yes refl = there a a xs (drop-map-lem f fp a xs p)
drop-map-lem f fp a (x ∷ xs) p | no neq = there a x xs (drop-map-lem f fp a xs (neq-there (f a) (f x) (λ ef → neq (fp a x ef)) (map f xs) p))

map-preserves-Sec : ∀{l} {A B : Set l} {{_ : Eq A}} (f : A → B) (fp : Injective f) (a : A) (xs : List A)
                  → Section drop-map-lem f fp a xs of map-preserves-in f a xs
map-preserves-Sec f fp a [] ()
map-preserves-Sec f fp a (x ∷ xs) p with a == x
map-preserves-Sec f fp a (.a ∷ xs) (here .(f a) .(map f xs)) | yes refl = refl
map-preserves-Sec f fp a (.a ∷ xs) (there .(f a) .(f a) .(map f xs) p) | yes refl rewrite sym (map-preserves-Sec f fp a xs p) = refl
... | no neq
  rewrite sym (map-preserves-Sec f fp a xs (neq-there (f a) (f x) (λ z → neq (fp a x z)) (map f xs) p))
    = neq-there-lem (f a) (f x) (λ z → neq (fp a x z)) (map f xs) p

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

