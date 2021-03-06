module Utility.List.Elem.MapProps {l l′}{A : Set l}{B : Set l′} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Map

map-preserves-Sec-helper : ∀(f : A → B) (pf : Injective f) (a : A) (xs : List A) (ys : List B)
                         → (eq : ys ≡ map f xs) → (p : f a ∈ ys)
                         → transport (λ zs → f a ∈ zs) eq p ≡ map-preserves-in f a xs (drop-map-lem-helper f pf a xs ys eq p)
map-preserves-Sec-helper f pf a [] .(f a ∷ ys) () (here .(f a) ys)
map-preserves-Sec-helper f pf a (x ∷ xs) ._ eq (here .(f a) ys) with pf (cons-inj-head eq) | cons-inj-tail eq
map-preserves-Sec-helper f pf a (.a ∷ xs) ._ refl (here .(f a) .(map f xs)) | refl | refl = refl
map-preserves-Sec-helper f pf a [] .(y ∷ ys) () (there .(f a) y ys p)
map-preserves-Sec-helper f pf a (x ∷ xs) .(y ∷ ys) eq (there .(f a) y ys p)
  rewrite sym (map-preserves-Sec-helper f pf a xs ys (cons-inj-tail eq) p)
     with eq
... | refl = refl


map-preserves-Sec : ∀(f : A → B) (fp : Injective f) (a : A) (xs : List A)
                  → Section drop-map-lem f fp a xs of map-preserves-in f a xs
map-preserves-Sec f fp a xs p = map-preserves-Sec-helper f fp a xs (map f xs) refl p

strong-map-preserves-prop : ∀{l′′}(f : A → B)(P : B → Set l′′)
                          → (xs : List A)
                          → (∀{a} → a ∈ xs → P (f a))
                          → {b : B}
                          → b ∈ map f xs
                          → P b
strong-map-preserves-prop f P [] pf ()
strong-map-preserves-prop f P (x ∷ xs) pf (here ._ ._) = pf (here x xs)
strong-map-preserves-prop f P (x ∷ xs) pf (there y ._ ._ el) = strong-map-preserves-prop f P xs (pf ∘ there _ _ _) el

map-preserves-prop : ∀{l′′}(f : A → B)(P : B → Set l′′)
                   → (∀ a → P (f a))
                   → (xs : List A)
                   → {b : B}
                   → b ∈ map f xs
                   → P b
map-preserves-prop f P pf xs el = strong-map-preserves-prop f P xs (λ {a} _ → pf a) el
