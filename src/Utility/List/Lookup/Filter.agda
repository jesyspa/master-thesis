import ThesisPrelude as TP
module Utility.List.Lookup.Filter {l}{A B : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Equality
open import Utility.List.Elem
open import Utility.List.Props
open import Utility.List.Lookup.Definition

filter-eq : ∀ (a : A) (xs : SearchList A B)
          → SearchList A B
filter-eq a = filter (isYes ∘ (_==_ a) ∘ fst)

filter-vals : ∀ (a : A) (xs : SearchList A B)
            → List B
filter-vals a = map snd ∘′ filter-eq a            

combine-vals : ∀{r : Set l} (cmb : List B → r) (a : A) (xs : SearchList A B) → r
combine-vals cmb a = cmb ∘ filter-vals a

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
