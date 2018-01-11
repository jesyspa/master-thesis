{-# OPTIONS --allow-unsolved-metas #-}
open import Carrier.Class using (Carrier; CarrierProps)
module Distribution.ListProps (Q : Set) {{QC : Carrier Q}} {{QCP : CarrierProps Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List Q
open import Algebra.Function
open import Algebra.Monoid
open import Carrier.Class
open import Utility.List.Props
open import Utility.List.Arithmetic
open import Utility.List.Lookup
open import Utility.Writer Q
open import Utility.Vector.BitVec
open import Utility.Product

import Algebra.FunctorComposition List Writer as FComp
open import Algebra.FunctorProps ListDist
instance
  private
    MonoidPropsMulQ : MonoidProps Q
    MonoidPropsMulQ = *-is-monoid

import Algebra.ApplicativeComposition List Writer as AComp
open import Algebra.ApplicativeProps ListDist

open import Algebra.MonadProps ListDist
postulate
  MonadPropsListDist : MonadProps

uniform-LD-is-uniform : ∀ n (v : BitVec n)
                      → negpow2 n ≡ sample-LD (uniform-LD n) v
uniform-LD-is-uniform n v =
  negpow2 n
    ≡⟨ singleton-sum-id (negpow2 n) ⟩
  sum [ negpow2 n ]
    ≡⟨ combine-vals-weak-invariant sum v
                                   (annotate (negpow2 n) (all-bitvecs n))
                                   ([ negpow2 n ])
                                   (all-bitvecs-filter-vals v (negpow2 n)) ⟩
  combine-vals sum v (annotate (negpow2 n) (all-bitvecs n))
  ∎
-- another attempt:
-- ≡⟨ combine-vals-invariant sum {!!} v
--      [ v , negpow2 {{QC}} n ]
--      (annotate (negpow2 {{QC}} n) (all-bitvecs n))
--      (all-bitvecs-indexing v (negpow2 {{QC}} n)) ⟩

uniform-LD-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                               → Bijective f 
                               → fmap f (uniform-LD n) ≡LD uniform-LD n
uniform-LD-bijection-invariant n f (bp , pa , pb) = {!!}

sample-invariant-LD : ∀ {A} {{_ : Eq A}} {xs ys : ListDist A} → xs ≡LD ys → (a : A) → sample-LD xs a ≡ sample-LD ys a
sample-invariant-LD (sample-equiv p) a = p a

open import Distribution.PropsClass ListDist

instance
  DistMonadPropsListDist : DistMonadProps
  DistMonadPropsListDist = record
                             { is-monad = MonadPropsListDist
                             ; uniform-is-uniform = uniform-LD-is-uniform
                             ; uniform-bijection-invariant = uniform-LD-bijection-invariant
                             ; sample-invariant = sample-invariant-LD
                             }
