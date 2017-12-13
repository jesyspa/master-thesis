module Algebra.Applicative where

open import ThesisPrelude
open import Algebra.Functor

record ApplicativeProps {l l'} (F : Set l → Set l') {{AP : Applicative F}} : Set (lsuc l ⊔ l') where
  field
    <*>-identity : ∀{A} (v : F A) → v ≡ (pure id <*> v)
    <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
                    → (u <*> (v <*> w)) ≡ (pure _∘′_ <*> u <*> v <*> w)
    <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → Applicative.pure AP (f x) ≡ (pure f <*> pure x)
    <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
    overlap {{super}} : FunctorProps F
    fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)

open ApplicativeProps {{...}} public
