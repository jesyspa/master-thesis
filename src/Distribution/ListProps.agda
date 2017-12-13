module Distribution.ListProps where

open import ThesisPrelude
open import Distribution.List
open import Algebra.Functor
open import Carrier.Class

-- C for Carrier was inconvenient so now it's Q for... Quarrier.

fmap-LD-id : ∀{A Q} (v : ListDist Q A)
           → v ≡ fmap-LD id v
fmap-LD-id [] = refl
fmap-LD-id ((a , q) ∷ v) rewrite sym (fmap-LD-id v) = refl

fmap-LD-comp : ∀{A B C Q} (g : B → C) (f : A → B) (v : ListDist Q A)
             → fmap (g ∘′ f) v ≡ fmap g (fmap f v)
fmap-LD-comp g f [] = refl
fmap-LD-comp g f ((a , q) ∷ v) rewrite fmap-LD-comp g f v = refl

instance
  FunctorPropsListDist : ∀{Q} → FunctorProps (ListDist Q)
  FunctorPropsListDist = record { fmap-id = fmap-LD-id ; fmap-comp = fmap-LD-comp }

