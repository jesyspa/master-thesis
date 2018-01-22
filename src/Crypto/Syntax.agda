module Crypto.Syntax where

open import ThesisPrelude
open import Utility.List
open import Utility.Vector.BitVec
open import Utility.Vector.Functions

OracleList : Set₁
OracleList = List (Set × Set)

data CryptoExpr : OracleList → Set → Set₁ where
  returnCE : ∀{O A} → A → CryptoExpr O A
  uniformCE : ∀{O A} n → (BitVec n → CryptoExpr O A) → CryptoExpr O A
  callOracleCE : ∀{O X Y A} → (X , Y) ∈ O → X → (Y → CryptoExpr O A) → CryptoExpr O A
  addOracleCE : ∀{O X Y A} → (X → Y) → (((X , Y) ∈ (X , Y) ∷ O) → CryptoExpr ((X , Y) ∷ O) A) → CryptoExpr O A
  weakenCE : ∀{O A} → (X Y : Set) → CryptoExpr O A → CryptoExpr ((X , Y) ∷ O) A


uniform-expr : ∀{O} n → CryptoExpr O (BitVec n)
uniform-expr n = uniformCE n returnCE

fmap-CE : ∀{O A B} → (A → B) → CryptoExpr O A → CryptoExpr O B
fmap-CE f (returnCE a) = returnCE (f a)
fmap-CE f (uniformCE n cont) = uniformCE n (λ z → fmap-CE f (cont z))
fmap-CE f (callOracleCE p x cont) = callOracleCE p x (λ z → fmap-CE f (cont z))
fmap-CE f (addOracleCE g cont) = addOracleCE g (λ z → fmap-CE f (cont z))
fmap-CE f (weakenCE X Y ce) = weakenCE X Y (fmap-CE f ce)

bind-CE : ∀{O A B} → CryptoExpr O A → (∀{O′} → A → CryptoExpr O′ B) → CryptoExpr O B
bind-CE (returnCE a) f = f a
bind-CE (uniformCE n cont) f = uniformCE n (λ z → bind-CE (cont z) f)
bind-CE (callOracleCE p a cont) f = callOracleCE p a (λ z → bind-CE (cont z) f)
bind-CE (addOracleCE g cont) f = addOracleCE g λ z → bind-CE (cont z) f 
bind-CE (weakenCE X Y ce) f = weakenCE X Y (bind-CE ce f)

{-
ap-CE : ∀{O A B} → CryptoExpr O (A → B) → CryptoExpr O A → CryptoExpr O B
ap-CE (returnCE f) e = fmap-CE f e
ap-CE (uniformCE n f) e = uniformCE n λ xs → ap-CE (f xs) e
ap-CE (callOracleCE p x cont) e = callOracleCE p x (λ z → ap-CE (cont z) e)
ap-CE (addOracleCE {X = X} {Y = Y} g cont) e = addOracleCE g λ z → ap-CE (cont z) (weakenCE X Y e)
ap-CE (weakenCE X Y ce) e = {!!}
-}

{-
bind-CE : ∀{A B} → CryptoExpr A → (A → CryptoExpr B) → CryptoExpr B
bind-CE (returnCE x) f = f x
bind-CE (uniformCE n x) f = uniformCE n (λ z → bind-CE (x z) f)

instance
  FunctorCryptoExpr : Functor CryptoExpr
  FunctorCryptoExpr = record { fmap = fmap-CE }
  ApplicativeCryptoExpr : Applicative CryptoExpr
  ApplicativeCryptoExpr = record { pure = returnCE ; _<*>_ = ap-CE }
  MonadCryptoExpr : Monad CryptoExpr 
  MonadCryptoExpr = record { _>>=_ = bind-CE }

coin-expr : CryptoExpr Bool
coin-expr = fmap head (uniform-expr 1)

-}
