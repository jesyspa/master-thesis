module Utility.List.Lookup.Definition where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Product
open import Utility.List.Elem
open import Utility.List.Props

SearchList : ∀ {l} (A B : Set l) → Set l
SearchList A B = List (A × B)

module _ {l} {A B : Set l} where
  data Index : A → SearchList A B → Set l where
    here : ∀ a b xs → Index a ((a , b) ∷ xs)
    there : ∀ a x xs → Index a xs → Index a (x ∷ xs)

  Index-there-Inj : ∀{a : A} {x : A × B} {xs : SearchList A B}
                  → Injective (Index.there a x xs)
  Index-there-Inj refl = refl

  annotate : (b : B) (xs : List A) → SearchList A B
  annotate = map ∘′ rev-pair 
