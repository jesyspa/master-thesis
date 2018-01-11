import ThesisPrelude using (Functor)
module Algebra.FunctorProps {l l′} (F : Set l → Set l′) {{FF : ThesisPrelude.Functor F}} where

open import ThesisPrelude
open import Algebra.Function

fmap-F : ∀{A B} → (A → B) → F A → F B
fmap-F = fmap 

record FunctorProps : Set (lsuc l ⊔ l′) where
  field
    fmap-ext : ∀{A B} (f g : A → B)
             → (∀ a → f a ≡ g a)
             → (x : F A)
             → fmap-F f x ≡ fmap-F g x
    fmap-id : ∀{A} → (x : F A) → x ≡ fmap-F id x
    fmap-comp : ∀{A B C} (g : B → C) (f : A → B) (x : F A) 
              → fmap-F (g ∘ f) x ≡ fmap-F g (fmap-F f x)
  fmap-ext-id : ∀{A} (f : A → A)
              → (∀ a → a ≡ f a)
              → (x : F A)
              → x ≡ fmap-F f x
  fmap-ext-id f p x = fmap-id x ⟨≡⟩ fmap-ext id f p x
  fmap-lift-ret : ∀{A B} (g : B → A) (f : A → B)
                → Retraction g of f
                → Retraction fmap-F g of fmap-F f
  fmap-lift-ret g f rp x = fmap-ext-id (g ∘′ f) rp x ⟨≡⟩ fmap-comp g f x

open FunctorProps

