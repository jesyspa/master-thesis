open import Carrier.Class using (Carrier; CarrierProps)
module Crypto.OTP (Q : Set) {{CQ : Carrier Q}} {{CPQ : CarrierProps Q}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.BitVec
open import Distribution.Class
open import Distribution.List Q
open import Distribution.ListProps Q
open import Distribution.PropsClass ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Carrier.Class
open DistMonad {{...}}
open DistMonadProps {{...}}
open MonadProps

expr-A : ∀ n (xs : BitVec n) → CryptoExpr (BitVec n)
expr-A n xs = fmap (bitvec-xor xs) (uniform-expr n)

expr-B : ∀ n → CryptoExpr (BitVec n)
expr-B n = uniform-expr n

otp-goal-list : ∀ (n : Nat) (xs : BitVec n)
              → ⟦ expr-A n xs ⟧ ≡D ⟦ expr-B n ⟧
otp-goal-list n xs = sample-equiv λ a →
  sample-LD ⟦ expr-A n xs ⟧ a
    ≡⟨ refl ⟩
  sample-LD (uniform-LD n >>= (λ ys → return (bitvec-xor xs ys))) a
    ≡⟨ cong (λ e → sample-LD e a) (sym (return-simplify MonadPropsListDist (bitvec-xor xs) (uniform-LD n))) ⟩
  sample-LD (fmap (bitvec-xor xs) (uniform-LD n)) a
    ≡⟨ sample-invariant (uniform-LD-bijection-invariant n (bitvec-xor xs) (bitvec-xor-Bij xs)) a ⟩
  sample-LD (uniform-LD n) a
    ≡⟨ cong (λ e → sample-LD e a) (return->>=-right-id MonadPropsListDist (uniform-LD n)) ⟩
  sample-LD (uniform-LD n >>= return {{MonadListDist}}) a
    ≡⟨ refl ⟩
  sample-LD (⟦ expr-B n ⟧) a
  ∎

