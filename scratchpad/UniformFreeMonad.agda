module UniformFreeMonad where

open import MyPrelude
open import AbstractDist
open import BitVec

data UniformFree (A : Set) : Set where
  returnUF : A → UniformFree A
  uniformUF : ∀ n → (BitVec n → UniformFree A) → UniformFree A

_>>=UF_ : ∀{A B} → UniformFree A → (A → UniformFree B) → UniformFree B
returnUF x >>=UF f = f x
uniformUF n x >>=UF f = uniformUF n (λ z → x z >>=UF f)

