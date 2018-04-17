module Utility.List.Elem.Functions where

open import ThesisPrelude
open import Algebra.Function
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Map
open import Utility.List.Elem.MapProps
open import Utility.List.Props

module _ {l}{A : Set l} where
  inject-element : (xs : List A)(x : A) → Elem xs → Elem (x ∷ xs)
  inject-element xs x (y , p) = y , there _ _ _ p

  inject-element-Inj : (xs : List A)(x : A) → Injective (inject-element xs x)
  inject-element-Inj xs x {a , p} {.a , .p} refl = refl

  list-elements : (xs : List A) → List (Elem xs)
  list-elements [] = []
  list-elements (x ∷ xs) = (x , here x _) ∷ map (inject-element xs x) (list-elements xs) 

  list-elements-map : ∀{l′}{B : Set l′}(xs : List A)(f : A → B) → map f xs ≡ map (f ∘′ fst) (list-elements xs)
  list-elements-map [] f = refl
  list-elements-map (x ∷ xs) f = cong (_∷_ (f x)) $
    map f xs
      ≡⟨ list-elements-map xs f ⟩
    map (f ∘′ fst) (list-elements xs) 
      ≡⟨ map-ext (f ∘′ fst) (f ∘′ fst ∘′ inject-element xs x) (λ { (e , p) → refl }) _ ⟩
    map (f ∘′ fst ∘′ inject-element xs x) (list-elements xs)
      ≡⟨ map-comp _ _ _ ⟩
    map (f ∘′ fst) (map (inject-element xs x) (list-elements xs))
    ∎


  list-elements-Complete : (xs : List A)(e : Elem xs) → e ∈ list-elements xs 
  list-elements-Complete .(x ∷ xs) (x , here .x xs)      = here (x , here x xs) _
  list-elements-Complete .(x ∷ xs) (y , there .y x xs p) = there _ _ _ (map-preserves-in _ _ _ (list-elements-Complete xs (y , p)))

  list-elements-lem : {xs : List A}{e : A}(ys : List (Elem xs))(p : (e , here e xs) ∈ map (inject-element xs e) ys) → ⊥
  list-elements-lem [] ()
  list-elements-lem ((y , q) ∷ ys) (there ._ ._ ._ p) = list-elements-lem ys p

  list-elements-Unique : (xs : List A)(e : Elem xs)(p : e ∈ list-elements xs) → p ≡ list-elements-Complete xs e
  list-elements-Unique [] (y , ()) p
  list-elements-Unique (x ∷ xs) (.x , here .x .xs) (here  .(x , here x xs) ._)      = refl
  list-elements-Unique (x ∷ xs) (.x , here .x .xs) (there .(x , here x xs) ._ ._ p) = ⊥-elim (list-elements-lem _ p)
  list-elements-Unique (x ∷ xs) (y , there .y .x .xs q) (there ._ ._ ._ p)
    = cong (there _ _ _) (map-preserves-RAdj (inject-element xs x)
                                             (inject-element-Inj xs x)
                                             (list-elements-Unique _ _ (drop-map-lem _ _ _ _ p)))
