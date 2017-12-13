module Crypto.Syntax where

open import ThesisPrelude
open import Utility.BitVec

data CryptoExpr (A : Set) : Set where
  returnCE : A → CryptoExpr A
  uniformCE : ∀ n → (BitVec n → CryptoExpr A) → CryptoExpr A

uniform-expr : ∀ n → CryptoExpr (BitVec n)
uniform-expr n = uniformCE n returnCE

fmap-CE : ∀{A B} → (A → B) → CryptoExpr A → CryptoExpr B
fmap-CE f (returnCE x) = returnCE (f x)
fmap-CE f (uniformCE n x) = uniformCE n (λ z → fmap-CE f (x z))

ap-CE : ∀{A B} → CryptoExpr (A → B) → CryptoExpr A → CryptoExpr B
ap-CE (returnCE f) e = fmap-CE f e
ap-CE (uniformCE n f) e = uniformCE n λ xs → ap-CE (f xs) e

bind-CE : ∀{A B} → CryptoExpr A → (A → CryptoExpr B) → CryptoExpr B
bind-CE (returnCE x) f = f x
bind-CE (uniformCE n x) f = uniformCE n (λ z → bind-CE (x z) f)

instance
  CryptoExprFunctor : Functor CryptoExpr
  CryptoExprFunctor = record { fmap = fmap-CE }
  CryptoExprApplicative : Applicative CryptoExpr
  CryptoExprApplicative = record { pure = returnCE ; _<*>_ = ap-CE }
  CryptoExprMonad : Monad CryptoExpr 
  CryptoExprMonad = record { _>>=_ = bind-CE }
