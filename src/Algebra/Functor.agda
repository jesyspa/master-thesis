module Algebra.Functor where

open import ThesisPrelude

record FunctorProps {l l'} (F : Set l → Set l') {{_ : Functor F}} : Set (lsuc l ⊔ l') where
  field
    -- Or id ≡ fmap id?  But without function extensionality that's hard to prove
    fmap-id : ∀{A} → (x : F A) → x ≡ fmap id x
    fmap-comp : ∀{A B C} (g : B → C) (f : A → B) (x : F A) 
              → fmap (g ∘ f) x ≡ fmap g (fmap f x)

open FunctorProps {{...}} public
