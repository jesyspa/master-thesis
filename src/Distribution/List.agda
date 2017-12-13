module Distribution.List where

open import ThesisPrelude
open import Carrier.Class

ListDist : ∀ (C : Set) (A : Set) → Set
ListDist C A = List (A × C)

fmap-LD : ∀{C A B} → (A → B) → ListDist C A → ListDist C B
fmap-LD f = map λ { (a , c) → f a , c }

pure-LD : ∀{C A} {{_ : Carrier C}} → A → ListDist C A
pure-LD a = [ a , one ]

bind-LD : ∀{C A B} {{_ : Carrier C}} → ListDist C A → (A → ListDist C B) → ListDist C B
bind-LD xs f = concatMap (λ { (a , c) → map (λ { (b , d) → b , c * d }) (f a) }) xs

ap-LD : ∀{C A B} {{_ : Carrier C}} → ListDist C (A → B) → ListDist C A → ListDist C B
ap-LD xs ys = bind-LD xs λ x → bind-LD ys λ y → pure-LD (x y)

instance
  ListDistFunctor : ∀{C} → Functor (ListDist C)
  ListDistFunctor = record { fmap = fmap-LD }
  ListDistApplicative :  ∀{C} {{_ : Carrier C}} → Applicative (ListDist C)
  ListDistApplicative = record { pure = pure-LD ; _<*>_ = ap-LD }
  ListDistMonad :  ∀{C} {{_ : Carrier C}} → Monad (ListDist C)
  ListDistMonad = record { _>>=_ = bind-LD }


