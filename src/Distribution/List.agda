module Distribution.List where

open import ThesisPrelude
open import Distribution.Class
open import Carrier.Class
open import Algebra.Functor
open import Utility.BitVec
open import Utility.Writer
open import Utility.Lookup

ListDist : ∀ (Q A : Set) → Set
ListDist Q A = SearchList A Q

instance
  FunctorListDist : ∀{Q} → Functor (ListDist Q)
  FunctorListDist {Q} = functor-composition List (Writer Q)

module _ {Q : Set} {{_ : Carrier Q}} where
  pure-LD : ∀{A} → A → ListDist Q A
  pure-LD a = [ a , one ]
  
  ap-LD-H2 : ∀{A B : Set} → (A → B) → Q → (A × Q) → B × Q 
  ap-LD-H2 f q (x , p) = f x , q * p

  ap-LD-H1 : ∀{A B} → ListDist Q A → (A → B) × Q → ListDist Q B
  ap-LD-H1 v (f , q) = map (ap-LD-H2 f q) v

  ap-LD : ∀{A B} → ListDist Q (A → B) → ListDist Q A → ListDist Q B
  ap-LD xs ys = concatMap (ap-LD-H1 ys) xs 

  bind-LD : ∀{A B} → ListDist Q A → (A → ListDist Q B) → ListDist Q B
  bind-LD xs f = concatMap (λ { (a , q) → map (ap-LD-H2 id q) (f a) }) xs
  
  instance
    ApplicativeListDist : Applicative (ListDist Q)
    ApplicativeListDist = record { pure = pure-LD ; _<*>_ = ap-LD }
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
