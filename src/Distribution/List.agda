open import Probability.Class using (Probability)
module Distribution.List (Q : Set) {{QC : Probability Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Probability.Class
open import Algebra.Monoid
open import Utility.Vector.BitVec
open import Utility.Writer Q {{*-monoid}}
open import Utility.List.Lookup

instance
  QMulMonoid : Monoid Q
  QMulMonoid = *-monoid

open import Algebra.FunctorProps 

ListDist : Set → Set
ListDist = List ∘′ Writer

import Algebra.FunctorComposition List Writer as FComp
instance
  FunctorListDist : Functor ListDist
  FunctorListDist = FComp.functor-composition

import Algebra.ApplicativeComposition List Writer as AComp
instance
  ApplicativeListDist : Applicative ListDist
  ApplicativeListDist = AComp.applicative-composition

import Utility.Writer.Transformer Q List as WriterT
instance
  MonadListDist : Monad ListDist
  MonadListDist = WriterT.writer-monad-composition

uniform-LD : (n : Nat) → ListDist (BitVec n)
uniform-LD n = annotate (negpow2 n) (all-bitvecs n)

sample-LD : ∀{A} {{_ : Eq A}} → ListDist A → A → Q
sample-LD dist a = combine-vals sum a dist

infix 4 _≡LD_
data _≡LD_ {A} {{_ : Eq A}} : ListDist A → ListDist A → Set where
  sample-equiv : {da db : ListDist A}
               → ((a : A) → sample-LD da a ≡ sample-LD db a)
               → da ≡LD db

instance
  DistMonadListDist : DistMonad ListDist
  DistMonadListDist = record { probability = Q
                             ; uniform = uniform-LD
                             ; sample = sample-LD
                             ; _≡D_ = _≡LD_
                             ; monad-super = MonadListDist
                             ; probability-super = QC
                             }
