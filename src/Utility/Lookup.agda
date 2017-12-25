{-# OPTIONS --allow-unsolved-metas #-}
module Utility.Lookup where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Functor
open import Algebra.Equality
open import Utility.Elem
open import Utility.ListLemmas
open import Utility.Permutation
open import Utility.Writer

SearchList : ∀ {l} (A B : Set l) → Set l
SearchList A B = List (A × B)


module _ {l} {A B : Set l} where
  data Index : A → SearchList A B → Set l where
    here : ∀ a b xs → Index a ((a , b) ∷ xs)
    there : ∀ a x xs → Index a xs → Index a (x ∷ xs)

  Index-there-Inj : ∀{a : A} {x : A × B} {xs : SearchList A B}
                  → Injective (Index.there a x xs)
  Index-there-Inj refl = refl
  
  Index-to-∈ : ∀(a : A) (xs : SearchList A B)
             → Index a xs → a ∈ map fst xs
  Index-to-∈ a .((a , b) ∷ xs) (here .a b xs) = here a (map fst xs)
  Index-to-∈ a .(x ∷ xs) (there .a x xs p) = there a (fst x) (map fst xs) (Index-to-∈ a xs p)

  Index-to-∈-Inj : ∀(a : A) (xs : SearchList A B)
                 → Injective (Index-to-∈ a xs)
  Index-to-∈-Inj a [] {()} {()} eq
  Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {here .a .b .xs} eq = refl
  Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {there .a .(a , b) .xs q} ()
  Index-to-∈-Inj a (.(a , b) ∷ xs) {there .a .(a , b) .xs p} {here .a b .xs} ()
  Index-to-∈-Inj a (x ∷ xs) {there .a .x .xs p} {there .a .x .xs q} eq
    rewrite Index-to-∈-Inj a xs (there-Inj eq) = refl

  Index-to-∈′ : ∀(a : A) (xs : List A) (f : A → A × B)
              → ((x : A) → x ≡ fst (f x))
              → Index a (map f xs) → a ∈ xs 
  Index-to-∈′ a xs f eq p = transport (_∈_ a) (sym $ fmap-lift-ret fst f eq xs) (Index-to-∈ a (map f xs) p)

  ∈-to-Index-helper : ∀ (a : A) (xs : SearchList A B) (as : List A)
                    → as ≡ map fst xs → a ∈ as → Index a xs
  ∈-to-Index-helper a [] ._ () (here .a as)
  ∈-to-Index-helper ._ (x ∷ xs) ._ refl (here ._ ._) with x
  ... | a , b = here a b xs
  ∈-to-Index-helper a [] ._ () (there .a y as p)
  ∈-to-Index-helper a (x ∷ xs) ._ refl (there .a ._ ._ p)
    = there a x xs (∈-to-Index-helper a xs (map fst xs) refl p)
  
  ∈-to-Index : ∀ (a : A) (xs : SearchList A B)
             → a ∈ map fst xs → Index a xs
  ∈-to-Index a xs p = ∈-to-Index-helper a xs (map fst xs) refl p

  ∈-to-Index′ : ∀(a : A) (xs : List A) (f : A → A × B)
              → ((x : A) → x ≡ fst (f x))
              → a ∈ xs → Index a (map f xs)
  ∈-to-Index′ a xs f eq p = ∈-to-Index a (map f xs) (transport (_∈_ a) (fmap-lift-ret fst f eq xs) p)

  ∈-to-Index-Ret : ∀(a : A) (xs : SearchList A B)
                 → Retraction ∈-to-Index a xs of Index-to-∈ a xs
  ∈-to-Index-Ret a .((a , b) ∷ xs) (here .a b xs) = refl
  ∈-to-Index-Ret a .(x ∷ xs) (there .a x xs p)
    rewrite sym (∈-to-Index-Ret a xs p) = refl

  Index-to-∈-Ret : ∀(a : A) (xs : SearchList A B)
                 → Retraction Index-to-∈ a xs of ∈-to-Index a xs
  Index-to-∈-Ret a [] ()
  Index-to-∈-Ret .(fst x) (x ∷ xs) (here .(fst x) .(map fst xs)) with x
  ... | a , b = refl
  Index-to-∈-Ret a (x ∷ xs) (there .a .(fst x) .(map fst xs) p) with x
  ... | a′ , b rewrite sym (Index-to-∈-Ret a xs p) = refl

  ∈-to-Index-Inj : ∀(a : A) (xs : SearchList A B)
                 → Injective (∈-to-Index a xs)
  ∈-to-Index-Inj a [] {()} {()} eq
  ∈-to-Index-Inj ._ (x ∷ xs) {here ._ ._} {here ._ ._} refl = refl
  ∈-to-Index-Inj ._ (x ∷ xs) {here ._ ._} {there ._ ._ ._ q} eq with x
  ∈-to-Index-Inj ._ (x ∷ xs) {here ._ ._} {there ._ ._ ._ q} () | a′ , b
  ∈-to-Index-Inj ._ (x ∷ xs) {there ._ ._ ._ p} {here ._ ._} eq with x
  ∈-to-Index-Inj ._ (x ∷ xs) {there ._ ._ ._ p} {here ._ ._} () | a′ , b
  ∈-to-Index-Inj a (x ∷ xs) {there .a ._ ._ p} {there .a ._ ._ q} eq with x
  ... | a′ , b rewrite sym (∈-to-Index-Inj a xs (Index-there-Inj eq)) = refl
  
  module _ {{_ : Eq A}} where
    filter-eq : ∀ (a : A) (xs : SearchList A B)
              → SearchList A B
    filter-eq a = filter (isYes ∘ (_==_ a) ∘ fst)
    
    filter-vals : ∀ (a : A) (xs : SearchList A B)
                → List B
    filter-vals a = map snd ∘′ filter-eq a            
    
    filter-eq-embed : ∀ (a : A) (xs : SearchList A B)
                    → Index a xs → Index a (filter-eq a xs)
    filter-eq-embed a .((a , b) ∷ xs) (here .a b xs) rewrite yes-refl a = here a b (filter-eq a xs)
    filter-eq-embed a .((a′ , b) ∷ xs) (there .a (a′ , b) xs ix) with a == a′
    ... | yes eq = there a (a′ , b) (filter-eq a xs) (filter-eq-embed a xs ix)
    ... | no neq = filter-eq-embed a xs ix
    
    filter-eq-extract-helper : ∀ (a : A) (xs ys : SearchList A B)
                             → ys ≡ filter-eq a xs → Index a ys
                             → Index a xs
    filter-eq-extract-helper a [] .((a , b) ∷ ys) () (here .a b ys)
    filter-eq-extract-helper a ((a′ , b′) ∷ xs) .((a , b) ∷ ys) xye (here .a b ys) with a == a′
    ... | yes refl = here a b′ xs
    ... | no neq = there a (a′ , b′) xs (filter-eq-extract-helper a xs ((a , b) ∷ ys) xye (here a b ys))
    filter-eq-extract-helper a [] .(x ∷ ys) () (there .a x ys p)
    filter-eq-extract-helper a ((a′ , b) ∷ xs) .(y ∷ ys) xye (there .a y ys p) with a == a′
    ... | yes refl = there a (a , b) xs (filter-eq-extract-helper a xs ys (cons-inj-tail xye) p)
    ... | no neq = there a (a′ , b) xs (filter-eq-extract-helper a xs (y ∷ ys) xye (there a y ys p))
    
    filter-eq-extract : ∀  (a : A) (xs : SearchList A B)
                      → Index a (filter-eq a xs) → Index a xs
    filter-eq-extract a xs p = filter-eq-extract-helper a xs (filter-eq a xs) refl p
    
    postulate
      filter-eq-embed-Sec : ∀ (a : A) (xs : SearchList A B)
                          → Section filter-eq-embed a xs of filter-eq-extract a xs
      filter-eq-embed-Ret : ∀ (a : A) (xs : SearchList A B)
                          → Retraction filter-eq-embed a xs of filter-eq-extract a xs
    
    filter-eq-correct : ∀ (a : A) (xs : SearchList A B)
                      → Index a xs ↔ Index a (filter-eq a xs)
    filter-eq-correct a xs = filter-eq-embed a xs , filter-eq-extract a xs , filter-eq-embed-Sec a xs , filter-eq-embed-Ret a xs

    filter-eq-idempotent : ∀(a : A) (xs : SearchList A B)
                         → filter-eq a xs ≡ filter-eq a (filter-eq a xs)
    filter-eq-idempotent a [] = refl
    filter-eq-idempotent a ((a′ , b) ∷ xs) with a == a′
    ... | yes refl rewrite yes-refl a | sym (filter-eq-idempotent a xs) = refl
    ... | no neq rewrite sym (filter-eq-idempotent a xs) = refl

    annotate : (b : B) (xs : List A) → SearchList A B
    annotate = map ∘′ make-W

    ∈-to-annotate-Index : ∀(a : A) (xs : List A) (b : B)
                        → a ∈ xs → Index a (annotate b xs)
    ∈-to-annotate-Index a xs b p = ∈-to-Index′ a xs (make-W b) (λ x → refl) p

    annotate-Index-to-∈ : ∀(a : A) (xs : List A) (b : B)
                        → Index a (annotate b xs) → a ∈ xs
    annotate-Index-to-∈ a xs b p = Index-to-∈′ a xs (make-W b) (λ x → refl) p

    map-fst-annotate-Ret : (b : B) → Retraction map fst of annotate b
    map-fst-annotate-Ret b xs = fmap-ext-id (fst ∘′ make-W b) (λ a → refl) xs ⟨≡⟩ map-comp fst (make-W b) xs

    comm-annotate : (a : A) (b : B) (xs : List A)
                  → annotate b (filter (isYes ∘ (_==_ a)) xs) ≡ filter-eq a (annotate b xs)
    comm-annotate a b [] = refl
    comm-annotate a b (x ∷ xs) with a == x 
    ... | yes eq rewrite comm-annotate a b xs = refl
    ... | no neq rewrite comm-annotate a b xs = refl

    combine-vals : ∀{r : Set l} (cmb : List B → r) (a : A) (xs : SearchList A B) → r
    combine-vals cmb a = cmb ∘ map snd ∘ filter-eq a

    postulate
      combine-vals-invariant : ∀{r : Set l} (cmb : List B → r) (_ : PermInvariant cmb) (a : A) (xs ys : SearchList A B)
                             → (Index a xs ↔ Index a ys)
                             → combine-vals cmb a xs ≡ combine-vals cmb a ys



