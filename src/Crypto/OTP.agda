module Crypto.OTP where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.BitVec
open import Distribution.Class
open import Crypto.Valuation

expr-A : ∀ n (xs : BitVec n) → CryptoExpr (BitVec n)
expr-A n xs = uniform-expr n >>= λ ys → return (bitvec-xor xs ys)

expr-B : ∀ n → CryptoExpr (BitVec n)
expr-B n = uniform-expr n

-- Or at least for *some* DistMonad.
otp-goal : ∀ M n xs → {{_ : DistMonad M}} →  eval expr-A n xs as M ≡D eval expr-B n as M
otp-goal M n xs = {!!}
