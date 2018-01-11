{-# OPTIONS --allow-unsolved-metas #-}
module Utility.Permutation where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Elem

module _ {l} {A : Set l} where
  Element : List A → Set l
  Element xs = Σ A λ x → x ∈ xs

  Permutation : List A → Set l
  Permutation xs = Σ (List A) λ ys → Element xs ↔ Element ys

  get-perm : ∀{xs : List A} (φ : Permutation xs) → List A
  get-perm = fst

  apply-perm : ∀{xs : List A} (φ : Permutation xs) → Element xs → Element (get-perm φ)
  apply-perm (_ , f , _) = f

  PermInvariant : ∀{r : Set l} (cmb : List A → r) → Set l
  PermInvariant cmb = ∀(xs : List A) (φ : Permutation xs) → cmb xs ≡ cmb (get-perm φ)

  elements-empty-lem : ∀ ys → Element ys ↔ Element [] → ys ≡ []
  elements-empty-lem [] _ = refl
  elements-empty-lem (y ∷ ys) (f , _) with f (y , here y ys)
  ... | x , ()

  drop-index : ∀ x xs → x ∈ xs → List A
  drop-index a .(a ∷ xs) (here .a xs) = xs
  drop-index a .(y ∷ xs) (there .a y xs p) = y ∷ drop-index a xs p

  data SameElem {xs} : {a b : A} → a ∈ xs → b ∈ xs → Set where
    Elem-refl : ∀ {a} → (p : a ∈ xs) → SameElem p p

  SameElem-step : ∀{x y z xs} (p : x ∈ xs) (q : y ∈ xs)
                → SameElem p q
                → SameElem (there x z xs p) (there y z xs q)
  SameElem-step {x} {.x} {z} {xs} p .p (Elem-refl .p) = Elem-refl (there x z xs p)

  update-dropped-index : ∀ x xs (p : x ∈ xs) y (ix : y ∈ xs) → ¬ SameElem p ix  → y ∈ drop-index x xs p
  update-dropped-index x .(x ∷ xs) (here .x xs) .x (here .x .xs) neq = ⊥-elim (neq (Elem-refl (here x xs)))
  update-dropped-index x .(x ∷ xs) (here .x xs) y (there .y .x .xs ix) _ = ix
  update-dropped-index x .(y ∷ xs) (there .x y xs p) .y (here .y .xs) _ = here y (drop-index x xs p)
  update-dropped-index x (z ∷ xs) (there .x .z .xs p) y (there .y .z .xs ix) neq
    = there y z (drop-index x xs p) (update-dropped-index x xs p y ix λ se → neq (SameElem-step p ix se))

  remove-head-helper : ∀ x xs y → (φ : Permutation (x ∷ xs)) → (p : y ∈ get-perm φ) → apply-perm φ (x , here x xs) ≡ (y , p) → Permutation xs
  remove-head-helper x xs y (ys , f , fi , pfr , pfs) p eq = ys′ , g , gi , pgr , pgs
    where ys′ : List A
          ys′ = drop-index y ys p
          f-el : Element xs → A
          f-el (x′ , q) with f (x′ , there x′ x xs q)
          ... | y′ , _ = y′
          g : Element xs → Element ys′
          g (x′ , q) with f (x′ , there x′ x xs q)
          ... | y′ , ix = y′ , update-dropped-index y ys p y′ ix neq
            where neq : SameElem p ix → ⊥
                  neq (Elem-refl _) = {!!}
          gi : Element ys′ → Element xs
          gi = {!!}
          pgr : Retraction gi of g
          pgr = {!!}
          pgs : Section gi of g
          pgs = {!!}

  remove-head : ∀{x xs} → Permutation (x ∷ xs) → Permutation xs
  remove-head {x} {xs} ([] , f) with elements-empty-lem (x ∷ xs) f
  ... | ()
  remove-head {x} {xs} (ys , f , rest) with f (x , here x xs) | graphAt f (x , here x xs)
  ... | y , p | ingraph eq = remove-head-helper x xs y (ys , f , rest) p eq
