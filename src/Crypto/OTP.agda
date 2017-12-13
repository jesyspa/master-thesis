module Crypto.OTP where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.BitVec
open import Distribution.Class
open import Distribution.List
open import Crypto.Valuation
open import Carrier.Class

expr-A : ∀ n (xs : BitVec n) → CryptoExpr (BitVec n)
expr-A n xs = fmap (bitvec-xor xs) (uniform-expr n)

expr-B : ∀ n → CryptoExpr (BitVec n)
expr-B n = uniform-expr n

-- Or at least for *some* DistMonad.
otp-goal : ∀ M n xs → {{_ : DistMonad M}} →  eval expr-A n xs as M ≡D eval expr-B n as M
otp-goal M n xs = {!!}

otp-goal-list : ∀{C} (n : Nat) (xs : BitVec n) {{_ : Carrier C}} →  eval expr-A n xs as ListDist C ≡D eval expr-B n as ListDist C
otp-goal-list {C} n xs = sample-equiv λ a →
  sample-LD (eval expr-A n xs as ListDist C) a
    ≡⟨ refl ⟩
  sample-LD (uniform-LD n >>= (λ ys → return (bitvec-xor xs ys))) a
    ≡⟨ {!!} ⟩ -- x >>= (return . f) ≡ f <$> x, yet to prove.
  sample-LD (fmap (bitvec-xor xs) (uniform-LD n)) a
    ≡⟨ {!!} ⟩ -- this is the hard part
  sample-LD (uniform-LD n) a
    ≡⟨ {!!} ⟩ -- monad laws
  sample-LD (uniform-LD n >>= pure-LD) a
    ≡⟨ refl ⟩
  sample-LD (eval expr-B n as ListDist C) a
  ∎
