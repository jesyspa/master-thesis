module Crypto.OTP where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.BitVec
open import Algebra.Monad
open import Distribution.Class
open import Distribution.List
open import Distribution.ListProps
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
    ≡⟨ cong (λ e → sample-LD e a) (sym (return-simplify {{_}} {{MonadPropsListDist}} (bitvec-xor xs) (uniform-LD n))) ⟩
  sample-LD (fmap (bitvec-xor xs) (uniform-LD n)) a
    ≡⟨ {!!} ⟩ -- this is the hard part
  sample-LD (uniform-LD n) a
    ≡⟨ cong (λ e → sample-LD e a) (return->>=-right-id {{_}} {{MonadPropsListDist}} (uniform-LD n)) ⟩
  sample-LD (uniform-LD n >>= pure-LD) a
    ≡⟨ refl ⟩
  sample-LD (eval expr-B n as ListDist C) a
  ∎
