open import Probability.Class using (Probability)
module Crypto.OTP (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.Vector.BitVec
open import Probability.PropsClass Q
open ProbabilityProps {{...}}
open import Distribution.Class
open import Distribution.List Q
open import Distribution.ListProps Q
open import Distribution.PropsClass ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Probability.Class
open DistMonad {{...}}
open DistMonadProps {{...}}
open MonadProps

expr-A : ∀ n → CryptoExpr (BitVec n)
expr-A n = uniform-expr n

expr-B : ∀ n (xs : BitVec n) → CryptoExpr (BitVec n)
expr-B n xs = fmap (bitvec-xor xs) (uniform-expr n)

module _ {{_ : ProbabilityProps}} where
  otp-goal-list : ∀ (n : Nat) (xs : BitVec n)
                → ⟦ expr-A n ⟧ ≡D ⟦ expr-B n xs ⟧
  otp-goal-list n xs = sample-equiv λ a →
    sample-LD (⟦ expr-A n ⟧) a
      ≡⟨ refl ⟩
    sample-LD (uniform-LD n >>= return {{MonadListDist}}) a
      ≡⟨ cong (λ e → sample-LD e a) (return->>=-right-id MonadPropsListDist (uniform-LD n)) ⟩ʳ
    sample-LD (uniform-LD n) a
      ≡⟨ sample-invariant (uniform-LD-bijection-invariant n (bitvec-xor xs) (bitvec-xor-Bij xs)) a ⟩
    sample-LD (fmap (bitvec-xor xs) (uniform-LD n)) a
      ≡⟨ cong (λ e → sample-LD e a) (return-simplify MonadPropsListDist (bitvec-xor xs) (uniform-LD n)) ⟩
    sample-LD (uniform-LD n >>= (λ ys → return (bitvec-xor xs ys))) a
      ≡⟨ refl ⟩
    sample-LD ⟦ expr-B n xs ⟧ a
    ∎
  
