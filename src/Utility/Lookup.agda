module Utility.Lookup where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Equality
open import Utility.Elem
open import Utility.ListLemmas

SearchList : ∀ {l} (A B : Set l) → Set l
SearchList A B = List (A × B)


module _ {l} {A B : Set l} where
  data Index : A → SearchList A B → Set l where
    here : ∀ a b xs → Index a ((a , b) ∷ xs)
    there : ∀ a x xs → Index a xs → Index a (x ∷ xs)
  
  Index-to-∈ : ∀ (a : A) (xs : SearchList A B)
             → Index a xs → a ∈ map fst xs
  Index-to-∈ a .((a , b) ∷ xs) (here .a b xs) = here a (map fst xs)
  Index-to-∈ a .(x ∷ xs) (there .a x xs p) = there a (fst x) (map fst xs) (Index-to-∈ a xs p)
  
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

    combine-els : ∀{r : Set l} (cmb : List B → r) (a : A) (xs : SearchList A B) → r
    combine-els cmb a = cmb ∘ map snd ∘ filter-eq a

