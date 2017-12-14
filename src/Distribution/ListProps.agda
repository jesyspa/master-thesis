{-# OPTIONS --allow-unsolved-metas #-}
module Distribution.ListProps where

open import ThesisPrelude
open import Distribution.List
open import Algebra.Functor
open import Algebra.Applicative
open import Algebra.Monad
open import Algebra.Monoid
open import Carrier.Class
open import Utility.ListLemmas
open import Utility.Writer

instance
  FunctorPropsListDist : ∀{Q} → FunctorProps (ListDist Q)
  FunctorPropsListDist {Q} = functor-prop-composition List (Writer Q)

module _ {Q} {{QC : Carrier Q}} where
  --  <*>-identity : ∀{A} (v : F A) → v ≡ (pure id <*> v)
  --  <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
  --                  → (u <*> (v <*> w)) ≡ (pure _∘′_ <*> u <*> v <*> w)
  --  <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → Applicative.pure AP (f x) ≡ (pure f <*> pure x)
  --  <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
  --  overlap {{super}} : FunctorProps F
  --  fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)
  ap-LD-identity : ∀{A} (v : ListDist Q A) → v ≡ (pure-LD id <*> v)
  ap-LD-identity v =
    v
      ≡⟨ {!!} ⟩
    map (ap-LD-H2 id one) v
      ≡⟨ unit-right (map (ap-LD-H2 id one) v) ⟩
    map (ap-LD-H2 id one) v ++ []
    ∎

  postulate
    ApplicativePropsListDist : ApplicativeProps (ListDist Q)
    MonadPropsListDist : MonadProps (ListDist Q)
