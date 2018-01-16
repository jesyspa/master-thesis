module Crypto.Syntax where

open import ThesisPrelude
open import Utility.Vector.BitVec
open import Utility.Vector.Functions

data CryptoExpr (A : Set) : Set where
  returnCE : A → CryptoExpr A
  uniformCE : ∀ n → (BitVec n → CryptoExpr A) → CryptoExpr A

uniform-expr : ∀ n → CryptoExpr (BitVec n)
uniform-expr n = uniformCE n returnCE

fmap-CE : ∀{A B} → (A → B) → CryptoExpr A → CryptoExpr B
fmap-CE f (returnCE a) = returnCE (f a)
fmap-CE f (uniformCE n cont) = uniformCE n (λ z → fmap-CE f (cont z))

ap-CE : ∀{A B} → CryptoExpr (A → B) → CryptoExpr A → CryptoExpr B
ap-CE (returnCE f) e = fmap-CE f e
ap-CE (uniformCE n f) e = uniformCE n λ xs → ap-CE (f xs) e

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
