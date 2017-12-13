module Distribution.List where

open import ThesisPrelude
open import Distribution.Class
open import Carrier.Class
open import Utility.BitVec

ListDist : ∀ (C : Set) (A : Set) → Set
ListDist C A = List (A × C)

fmap-LD : ∀{C A B} → (A → B) → ListDist C A → ListDist C B
fmap-LD f = map λ { (a , c) → f a , c }

instance
  FunctorListDist : ∀{C} → Functor (ListDist C)
  FunctorListDist = record { fmap = fmap-LD }

module _ {C : Set} {{_ : Carrier C}} where
  pure-LD : ∀{A} → A → ListDist C A
  pure-LD a = [ a , one ]
  
  bind-LD : ∀{A B} → ListDist C A → (A → ListDist C B) → ListDist C B
  bind-LD xs f = concatMap (λ { (a , c) → map (λ { (b , d) → b , c * d }) (f a) }) xs
  
  ap-LD : ∀{A B} → ListDist C (A → B) → ListDist C A → ListDist C B
  ap-LD xs ys = bind-LD xs λ x → bind-LD ys λ y → pure-LD (x y)

  instance
    ApplicativeListDist : Applicative (ListDist C)
    ApplicativeListDist = record { pure = pure-LD ; _<*>_ = ap-LD }
    MonadListDist : Monad (ListDist C)
    MonadListDist = record { _>>=_ = bind-LD }

  uniform-LD : (n : Nat) → ListDist C (BitVec n)
  uniform-LD n = map (λ xs → xs , negpow2 n) (all-bitvecs n)
  
  sample-LD : ∀{A} {{_ : Eq A}} → ListDist C A → A → C
  sample-LD dist a = sum (map snd (filter (λ { (a' , _) → isYes (a == a')}) dist)) 
  
  infix 4 _≡LD_
  data _≡LD_ {A} {{_ : Eq A}} : ListDist C A → ListDist C A → Set where
    sample-equiv : {da db : ListDist C A}
                 → ((a : A) → sample-LD da a ≡ sample-LD db a)
                 → da ≡LD db

  instance
    DistMonadListDist : DistMonad (ListDist C)
    DistMonadListDist = record { carrier = C ; uniform = uniform-LD ; sample = sample-LD ; _≡D_ = _≡LD_ }
