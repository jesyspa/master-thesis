open import Probability.Class using (Probability; ProbabilityProps)
module Distribution.ListProps (Q : Set) {{QC : Probability Q}} {{QCP : ProbabilityProps Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List Q
open import Algebra.Function
open import Algebra.Monoid
open import Algebra.Equality
open import Probability.Class
open import Utility.List.Props
open import Utility.List.Arithmetic
open import Utility.List.Lookup
open import Utility.List.LookupProps
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

injections-preserve-filter : ∀{A B} {{_ : Eq A}} {{_ : Eq B}} (f : A → B)
                                → Injective f
                                → (D : ListDist A)
                                → (a : A)
                                → filter-vals a D ≡ filter-vals (f a) (fmap f D)
injections-preserve-filter f pf [] a = refl
injections-preserve-filter f pf ((x , v) ∷ D) a with a == x
... | yes refl rewrite yes-refl (f a) = cong (_∷_ v) (injections-preserve-filter f pf D a)
... | no neq with f a == f x
injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | yes eq = ⊥-elim (neq (pf eq))
injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | no neq′ = injections-preserve-filter f pf D a

injections-preserve-distributions-LD : ∀{A B} {{_ : Eq A}} {{_ : Eq B}} (f : A → B)
                                     → Injective f
                                     → (D : ListDist A)
                                     → (a : A)
                                     → sample-LD D a ≡ sample-LD (fmap f D) (f a)
injections-preserve-distributions-LD f pf D a = cong sum (injections-preserve-filter f pf D a)

uniform-LD-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                               → Bijective f 
                               → uniform-LD n ≡LD fmap f (uniform-LD n)
uniform-LD-bijection-invariant n f (fi , pa , pb) = sample-equiv λ v →
  sample-LD (uniform-LD n) v
    ≡⟨ uniform-LD-is-uniform n v  ⟩ʳ
  negpow2 n
    ≡⟨ uniform-LD-is-uniform n (fi v) ⟩
  sample-LD (uniform-LD n) (fi v)
    ≡⟨ injections-preserve-distributions-LD f (Bij-to-Inj f (fi , pa , pb)) (uniform-LD n) (fi v) ⟩
  sample-LD (fmap f (uniform-LD n)) (f (fi v))
    ≡⟨ cong (λ e → sample-LD (fmap f (uniform-LD n)) e) (pb v) ⟩ʳ
  sample-LD (fmap f (uniform-LD n)) v
  ∎

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
