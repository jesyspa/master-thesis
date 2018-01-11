open import Carrier.Class using (Carrier)
module Distribution.List (Q : Set) {{QC : Carrier Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Carrier.Class
open import Algebra.Monoid
open import Utility.BitVec
open import Utility.Writer Q {{*-monoid}}
open import Utility.Lookup

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

ap-LD-H2 : ∀{A : Set} → Q → (A × Q) → A × Q 
ap-LD-H2 q (x , p) = x , q * p

bind-LD : ∀{A B} → ListDist A → (A → ListDist B) → ListDist B
bind-LD xs f = concatMap (λ { (a , q) → map (ap-LD-H2 q) (f a) }) xs

open import Algebra.ApplicativeComposition List Writer 
instance
  ApplicativeListDist : Applicative ListDist
  ApplicativeListDist = applicative-composition
  MonadListDist : Monad ListDist
  MonadListDist = record { _>>=_ = bind-LD }

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
  DistMonadListDist = record { carrier = Q
                             ; uniform = uniform-LD
                             ; sample = sample-LD
                             ; _≡D_ = _≡LD_
                             ; monad-structure = MonadListDist
                             ; carrier-structure = QC
                             }
