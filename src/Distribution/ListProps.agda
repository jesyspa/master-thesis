{-# OPTIONS --allow-unsolved-metas #-}
module Distribution.ListProps where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List
open import Algebra.Functor
open import Algebra.Function
open import Algebra.Applicative
open import Algebra.ApplicativeComposition
open import Algebra.Monad
open import Algebra.Monoid
open import Carrier.Class
open import Utility.ListLemmas
open import Utility.ListArithmeticLemmas
open import Utility.Writer
open import Utility.BitVec
open import Utility.Product
open import Utility.Lookup

module _ {Q} {{QC : Carrier Q}} {{QCP : CarrierProps Q}} where
  instance
    private
      MonoidPropsMulQ : MonoidProps Q
      MonoidPropsMulQ = *-is-monoid
    FunctorPropsListDist : FunctorProps (ListDist Q)
    FunctorPropsListDist = functor-props-composition List QWriter

  ApplicativePropsListDist : ApplicativeProps (ListDist Q)
  ApplicativePropsListDist = applicative-props-composition List QWriter

  postulate
    MonadPropsListDist : MonadProps (ListDist Q)

  uniform-LD-is-uniform : ∀ n (v : BitVec n)
                        → negpow2 {{QC}} n ≡ sample-LD (uniform-LD n) v
  uniform-LD-is-uniform n v =
    negpow2 n
      ≡⟨ singleton-sum-id (negpow2 n) ⟩
    sum [ negpow2 n ]
      ≡⟨ cong sum (filter-eq-singleton v (negpow2 n)) ⟩
    combine-vals sum v ([ v , negpow2 n ])
      ≡⟨ combine-vals-invariant sum {!!} v [ v , negpow2 n ] (annotate (negpow2 n) (all-bitvecs n)) (all-bitvecs-indexing v (negpow2 n)) ⟩
    combine-vals sum v (annotate (negpow2 n) (all-bitvecs n))
    ∎

  uniform-LD-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                                 → Bijective f 
                                 → _≡LD_ {Q} (uniform-LD n) (fmap f (uniform-LD n))
  uniform-LD-bijection-invariant n f (bp , pa , pb) = {!!}

  DistMonadPropsListDist : DistMonadProps (ListDist Q)
  DistMonadPropsListDist = record
                             { is-monad = MonadPropsListDist
                             ; uniform-is-uniform = uniform-LD-is-uniform
                             ; uniform-bijection-invariant = uniform-LD-bijection-invariant
                             }
