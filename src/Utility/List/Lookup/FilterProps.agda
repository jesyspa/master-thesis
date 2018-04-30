import ThesisPrelude as TP
module Utility.List.Lookup.FilterProps {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Equality
open import Utility.Product
open import Utility.List.Elem
open import Utility.List.Props
open import Utility.List.Lookup.Definition
open import Utility.List.Lookup.Filter

module _ {B : Set l} where
  filter-eq-idempotent : ∀(a : A) (xs : SearchList A B)
                       → filter-eq a xs ≡ filter-eq a (filter-eq a xs)
  filter-eq-idempotent a [] = refl
  filter-eq-idempotent a ((a′ , b) ∷ xs) with a == a′
  ... | yes refl rewrite yes-refl a | sym (filter-eq-idempotent a xs) = refl
  ... | no neq rewrite sym (filter-eq-idempotent a xs) = refl
  
  filter-eq-singleton : ∀(a : A) (b : B)
                      → [ b ] ≡ filter-vals a [ a , b ]
  filter-eq-singleton a b rewrite yes-refl a = refl

  filter-eq-correct : {p : A × B}(a : A)(xs : SearchList A B) 
                    → p ∈ filter-eq a xs → p ∈ xs
  filter-eq-correct a xs = filter-does-not-add-elements _ xs (isYes ∘ (_==_ a) ∘ fst)

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
                  → map f (filter-vals a xs) ≡ filter-vals a (map (second f) xs)
  filter-vals-map f [] a = refl
  filter-vals-map f ((a′ , b) ∷ xs) a with a == a′
  ... | yes refl rewrite sym (filter-vals-map f xs a) = refl
  ... | no neq rewrite no-neq a a′ neq | sym (filter-vals-map f xs a) = refl

  not-in-filter-empty : (a : A) (xs : SearchList A B)
                      → ¬ (Index a xs) → [] ≡ filter-vals a xs
  not-in-filter-empty a [] np = refl
  not-in-filter-empty a ((a′ , b) ∷ xs) np with a == a′
  ... | yes refl = ⊥-elim $ np (here a b xs)
  ... | no neq = not-in-filter-empty a xs λ x → np (there a (a′ , b) xs x)

  injections-preserve-filter : ∀{A′} {{_ : Eq A′}} (f : A → A′)
                                  → Injective f
                                  → (xs : SearchList A B)
                                  → (a : A)
                                  → filter-vals a xs ≡ filter-vals (f a) (map (first f) xs)
  injections-preserve-filter f pf [] a = refl
  injections-preserve-filter f pf ((x , v) ∷ D) a with a == x
  ... | yes refl rewrite yes-refl (f a) = cong (_∷_ v) (injections-preserve-filter f pf D a)
  ... | no neq with f a == f x
  injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | yes eq = ⊥-elim (neq (pf eq))
  injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | no neq′ = injections-preserve-filter f pf D a
  

filter-vals-diag : (xs : List A) (a : A)
                 → filter (isYes ∘ (_==_ a)) xs ≡ filter-vals a (map diag xs)
filter-vals-diag [] a = refl
filter-vals-diag (x ∷ xs) a with a == x
... | yes refl rewrite sym (filter-vals-diag xs a) = refl
... | no neq rewrite sym (filter-vals-diag xs a) = refl


