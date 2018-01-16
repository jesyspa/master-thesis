module Utility.List.LookupProps where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Equality
open import Utility.Product
open import Utility.List.Elem
open import Utility.List.ElemProps
open import Utility.List.Props
open import Utility.List.Lookup
open import Utility.Writer

module _ {l} {A B : Set l} where
  Index-to-∈-Inj : ∀(a : A) (xs : SearchList A B)
                 → Injective (Index-to-∈ a xs)
  Index-to-∈-Inj a [] {()} {()} eq
  Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {here .a .b .xs} eq = refl
  Index-to-∈-Inj a (.(a , b) ∷ xs) {here .a b .xs} {there .a .(a , b) .xs q} ()
  Index-to-∈-Inj a (.(a , b) ∷ xs) {there .a .(a , b) .xs p} {here .a b .xs} ()
  Index-to-∈-Inj a (x ∷ xs) {there .a .x .xs p} {there .a .x .xs q} eq
    rewrite Index-to-∈-Inj a xs (there-Inj eq) = refl

  ∈-to-Index-Ret : ∀(a : A) (xs : SearchList A B)
                 → Retraction ∈-to-Index a xs of Index-to-∈ a xs
  ∈-to-Index-Ret a .((a , b) ∷ xs) (here .a b xs) = refl
  ∈-to-Index-Ret a .(x ∷ xs) (there .a x xs p)
    rewrite sym (∈-to-Index-Ret a xs p) = refl

  Index-to-∈-Ret : ∀(a : A) (xs : SearchList A B)
                 → Retraction Index-to-∈ a xs of ∈-to-Index a xs
  Index-to-∈-Ret a [] ()
  Index-to-∈-Ret ._ ((a , b) ∷ xs) (here ._ ._) = refl
  Index-to-∈-Ret a ((a′ , b) ∷ xs) (there .a ._ .(map fst xs) p)
      rewrite sym (Index-to-∈-Ret a xs p) = refl

  ∈-to-Index-Inj : ∀(a : A) (xs : SearchList A B)
                 → Injective (∈-to-Index a xs)
  ∈-to-Index-Inj a [] {()} {()} eq
  ∈-to-Index-Inj ._ (_ ∷ _) {here ._ ._} {here ._ ._} refl = refl
  ∈-to-Index-Inj ._ ((a′ , b) ∷ xs) {here ._ ._} {there ._ ._ ._ _} ()
  ∈-to-Index-Inj ._ ((a′ , b) ∷ xs) {there ._ ._ ._ _} {here ._ ._} ()
  ∈-to-Index-Inj a ((a′ , b) ∷ xs) {there .a ._ ._ _} {there .a ._ ._ _} eq
      rewrite sym (∈-to-Index-Inj a xs (Index-there-Inj eq)) = refl
  
  module _ {{_ : Eq A}} where
    postulate
      filter-eq-embed-Sec : ∀ (a : A) (xs : SearchList A B)
                          → Section filter-eq-embed a xs of filter-eq-extract a xs
      filter-eq-embed-Ret : ∀ (a : A) (xs : SearchList A B)
                          → Retraction filter-eq-embed a xs of filter-eq-extract a xs
    
    filter-eq-correct : ∀ (a : A) (xs : SearchList A B)
                      → Index a xs ↔ Index a (filter-eq a xs)
    filter-eq-correct a xs = filter-eq-embed a xs , filter-eq-extract a xs , filter-eq-embed-Sec a xs , filter-eq-embed-Ret a xs

    map-fst-annotate-Ret : (b : B) → Retraction map fst of annotate {A = A} b
    map-fst-annotate-Ret b xs = map-ext-id (fst ∘′ rev-pair b) (λ a → refl) xs ⟨≡⟩ map-comp fst (rev-pair b) xs

    map-snd-annotate-const : (b : B) → (xs : List A) → map (const b) xs ≡ map snd (annotate b xs)
    map-snd-annotate-const b [] = refl
    map-snd-annotate-const b (x ∷ xs) rewrite sym (map-snd-annotate-const b xs) = refl

    map-snd-annotate-replicate : (b : B) → (xs : List A) → replicate (length xs) b ≡ map snd (annotate b xs)
    map-snd-annotate-replicate b xs = map-const b xs ⟨≡⟩ map-snd-annotate-const b xs

    comm-annotate : (a : A) (b : B) (xs : List A)
                  → annotate b (filter (isYes ∘ (_==_ a)) xs) ≡ filter-eq a (annotate b xs)
    comm-annotate a b [] = refl
    comm-annotate a b (x ∷ xs) with a == x 
    ... | yes eq rewrite comm-annotate a b xs = refl
    ... | no neq rewrite comm-annotate a b xs = refl

    combine-vals-weak-invariant : ∀{r : Set l} (cmb : List B → r) (a : A) (xs : SearchList A B) (ys : List B)
                                → ys ≡ filter-vals a xs
                                → cmb ys ≡ combine-vals cmb a xs
    combine-vals-weak-invariant cmb a xs ._ refl = refl

    filter-vals-append-dist : (xs ys : SearchList A B)
                   → (a : A)
                   → filter-vals a (xs ++ ys) ≡ filter-vals a xs ++ filter-vals a ys
    filter-vals-append-dist xs ys a =
      map snd (filter (isYes ∘ (_==_ a) ∘ fst) (xs ++ ys))
        ≡⟨ cong (map snd) (filter-append-dist (isYes ∘ (_==_ a) ∘ fst) xs ys ) ⟩
      map snd (filter (isYes ∘ (_==_ a) ∘ fst) xs ++ filter (isYes ∘ (_==_ a) ∘ fst) ys)
        ≡⟨ map-append-dist snd (filter (isYes ∘ (_==_ a) ∘ fst) xs) (filter (isYes ∘ (_==_ a) ∘ fst) ys)  ⟩
      map snd (filter (isYes ∘ (_==_ a) ∘ fst) xs) ++ map snd (filter (isYes ∘ (_==_ a) ∘ fst) ys)
      ∎


    filter-vals-concat : (xss : List (SearchList A B))
                       → (a : A)
                       → filter-vals a (concat xss) ≡ concat (map (filter-vals a) xss)
    filter-vals-concat [] a = refl
    filter-vals-concat ([] ∷ xss) a = filter-vals-concat xss a
    filter-vals-concat (((a′ , b) ∷ xs) ∷ xss) a
        rewrite sym (filter-vals-concat xss a)
        with a == a′
    ... | yes refl rewrite sym (filter-vals-append-dist xs (concat xss) a) = refl
    ... | no neq = filter-vals-append-dist xs (concat xss) a 

    
    filter-vals-map : ∀{B′}  (f : B → B′) (xs : SearchList A B)(a : A)
                    → filter-vals a (map (over-snd f) xs) ≡ map f (filter-vals a xs)
    filter-vals-map f [] a = refl
    filter-vals-map f ((a′ , b) ∷ xs) a with a == a′
    ... | yes refl rewrite sym (filter-vals-map f xs a) = refl
    ... | no neq rewrite no-neq a a′ neq | sym (filter-vals-map f xs a) = refl
