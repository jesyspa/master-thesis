module Utility.Writer where

open import ThesisPrelude
open import Algebra.Functor

Writer : ∀ (Q A : Set) → Set
Writer Q A = A × Q

fmap-W : ∀{Q A B : Set} → (A → B) → Writer Q A → Writer Q B 
fmap-W f (a , q) = f a , q

fmap-W-ext : ∀{A B Q} (f g : A → B)
               → (∀ a → f a ≡ g a)
               → (x : Writer Q A)
               → fmap-W f x ≡ fmap-W g x
fmap-W-ext f g p (a , q) rewrite p a = refl

fmap-W-id : ∀{A Q}
              → (x : Writer Q A)
              → x ≡ fmap-W id x
fmap-W-id (a , q) = refl 

fmap-W-comp : ∀{A B C Q} (g : B → C) (f : A → B) (x : Writer Q A)
                → fmap-W (g ∘′ f) x ≡ fmap-W g (fmap-W f x)
fmap-W-comp g f (a , q) = refl

instance
  FunctorWriter : ∀{Q} → Functor (Writer Q)
  FunctorWriter = record { fmap = fmap-W }

  FunctorPropsWriter : ∀{Q} → FunctorProps (Writer Q)
  FunctorPropsWriter = record { fmap-ext = fmap-W-ext ; fmap-id = fmap-W-id ; fmap-comp = fmap-W-comp }

