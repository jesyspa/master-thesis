module Distribution.List where

open import ThesisPrelude
open import Distribution.Class
open import Carrier.Class
open import Algebra.Functor
open import Algebra.ApplicativeComposition
open import Algebra.Monoid
open import Utility.BitVec
open import Utility.Writer
open import Utility.Lookup

ListDist : ∀ (Q : Set) {{QC : Carrier Q}} → Set → Set
ListDist Q A = List (Writer Q {{*-monoid}} A)

module _ {Q : Set} {{QC : Carrier Q}} where
  QWriter : Set → Set
  QWriter = Writer Q {{*-monoid}}
  instance
    QMulMonoid : Monoid Q
    QMulMonoid = *-monoid
    FunctorQWriter : Functor QWriter
    FunctorQWriter = FunctorWriter 
    ApplicativeQWriter : Applicative QWriter
    ApplicativeQWriter = ApplicativeWriter
  instance
    FunctorListDist : Functor (ListDist Q)
    FunctorListDist = functor-composition List QWriter

  ap-LD-H2 : ∀{A : Set} → Q → (A × Q) → A × Q 
  ap-LD-H2 q (x , p) = x , q * p

  bind-LD : ∀{A B} → ListDist Q A → (A → ListDist Q B) → ListDist Q B
  bind-LD xs f = concatMap (λ { (a , q) → map (ap-LD-H2 q) (f a) }) xs
  
  instance
    ApplicativeListDist : Applicative (ListDist Q)
    ApplicativeListDist = applicative-composition List QWriter
    MonadListDist : Monad (ListDist Q)
    MonadListDist = record { _>>=_ = bind-LD }

  uniform-LD : (n : Nat) → ListDist Q (BitVec n)
  uniform-LD n = annotate (negpow2 n) (all-bitvecs n)
  
  sample-LD : ∀{A} {{_ : Eq A}} → ListDist Q A → A → Q
  sample-LD dist a = combine-vals sum a dist
  
  infix 4 _≡LD_
  data _≡LD_ {A} {{_ : Eq A}} : ListDist Q A → ListDist Q A → Set where
    sample-equiv : {da db : ListDist Q A}
                 → ((a : A) → sample-LD da a ≡ sample-LD db a)
                 → da ≡LD db

  instance
    DistMonadListDist : DistMonad (ListDist Q)
    DistMonadListDist = record { carrier = Q ; uniform = uniform-LD ; sample = sample-LD ; _≡D_ = _≡LD_ }
