{-# OPTIONS --allow-unsolved-metas #-}
module Distribution.ListProps where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List
open import Algebra.Functor
open import Algebra.Function
open import Algebra.Applicative
open import Algebra.Monad
open import Algebra.Monoid
open import Carrier.Class
open import Utility.ListLemmas
open import Utility.Writer
open import Utility.BitVec
open import Utility.Product
open import Utility.Lookup

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
  {-
  ap-LD-identity : ∀{A} (v : ListDist Q A) → v ≡ (pure-LD id <*> v)
  ap-LD-identity v =
    v
      ≡⟨ {!!} ⟩
    map (ap-LD-H2 id one) v
      ≡⟨ unit-right (map (ap-LD-H2 id one) v) ⟩
    map (ap-LD-H2 id one) v ++ []
    ∎
    -}

  postulate
    ApplicativePropsListDist : ApplicativeProps (ListDist Q)
    MonadPropsListDist : MonadProps (ListDist Q)

  uniform-LD-is-uniform : ∀{{QPC : CarrierProps Q}} n (v : BitVec n)
                        → negpow2 {{QC}} n ≡ sample-LD (uniform-LD n) v
  uniform-LD-is-uniform n v =
    negpow2 n
      ≡⟨ {!!} ⟩
    sum [ negpow2 n ]
      ≡⟨ cong sum (filter-eq-singleton v (negpow2 n)) ⟩
    combine-vals sum v ([ v , negpow2 n ])
      ≡⟨ combine-vals-invariant sum {!!} v ([ v , negpow2 n ]) (annotate (negpow2 n) (all-bitvecs n)) (all-bitvecs-indexing v (negpow2 n)) ⟩
    combine-vals sum v (annotate (negpow2 n) (all-bitvecs n))
    ∎

  uniform-LD-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                                 → Bijective f 
                                 → _≡LD_ {Q} (uniform-LD n) (fmap f (uniform-LD n))
  uniform-LD-bijection-invariant n f (bp , pa , pb) = {!!}

  DistMonadPropsListDist : {{QPC : CarrierProps Q}} → DistMonadProps (ListDist Q)
  DistMonadPropsListDist = record
                             { is-monad = MonadPropsListDist
                             ; uniform-is-uniform = uniform-LD-is-uniform
                             ; uniform-bijection-invariant = uniform-LD-bijection-invariant
                             }
