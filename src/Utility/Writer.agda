module Utility.Writer where

open import ThesisPrelude
open import Algebra.Functor

Writer : ∀ {l} (Q A : Set l) → Set l
Writer Q A = A × Q

module _ {l} {Q : Set l} where
  fmap-W : ∀{A B : Set l} → (A → B) → Writer Q A → Writer Q B 
  fmap-W f (a , q) = f a , q
  
  fmap-W-ext : ∀{A B} (f g : A → B)
                 → (∀ a → f a ≡ g a)
                 → (x : Writer Q A)
                 → fmap-W f x ≡ fmap-W g x
  fmap-W-ext f g p (a , q) rewrite p a = refl
  
  fmap-W-id : ∀{A}
                → (x : Writer Q A)
                → x ≡ fmap-W id x
  fmap-W-id (a , q) = refl 
  
  fmap-W-comp : ∀{A B C} (g : B → C) (f : A → B) (x : Writer Q A)
                  → fmap-W (g ∘′ f) x ≡ fmap-W g (fmap-W f x)
  fmap-W-comp g f (a , q) = refl
  
  make-W : ∀{A} → Q → A → Writer Q A
  make-W q a = a , q
  
  instance
    FunctorWriter : Functor (Writer Q)
    FunctorWriter = record { fmap = fmap-W }
  
    FunctorPropsWriter : FunctorProps (Writer Q)
    FunctorPropsWriter = record { fmap-ext = fmap-W-ext ; fmap-id = fmap-W-id ; fmap-comp = fmap-W-comp }
  
