import Probability.Class as PC
import Probability.PropsClass as PPC
module Crypto.OTP (Q : Set) {{PQ : PC.Probability Q}} {{PPQ : PPC.ProbabilityProps Q}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Utility.Vector
open import Utility.Bool
open import Probability.Class
open import Probability.PropsClass Q
open Probability PQ
open ProbabilityProps PPQ
open import Distribution.Class
open import Distribution.List Q
open import Distribution.ListProps Q
open import Distribution.PropsClass ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Probability.Class
open DistMonad DistMonadListDist
open DistMonadProps DistMonadPropsListDist
open MonadProps is-monad

expr-A : ∀ n → CryptoExpr (BitVec n)
expr-A n = uniform-expr n

expr-B : ∀ n (xs : BitVec n) → CryptoExpr (BitVec n)
expr-B n xs = fmap (bitvec-xor xs) (uniform-expr n)

otp-goal-list : ∀ (n : Nat) (xs : BitVec n)
              → ⟦ expr-A n ⟧ ≡D ⟦ expr-B n xs ⟧
otp-goal-list n xs = sample-equiv λ a →
  sample (⟦ expr-A n ⟧) a
    ≡⟨ refl ⟩
  sample (uniform n >>= return {{MonadListDist}}) a
    ≡⟨ cong (λ e → sample e a) (return->>=-right-id (uniform n)) ⟩ʳ
  sample (uniform n) a
    ≡⟨ sample-invariant (uniform-LD-bijection-invariant n (bitvec-xor xs) (bitvec-xor-Bij xs)) a ⟩
  sample (fmap (bitvec-xor xs) (uniform n)) a
    ≡⟨ cong (λ e → sample-LD e a) (return-simplify (bitvec-xor xs) (uniform n)) ⟩
  sample (uniform n >>= (λ ys → return (bitvec-xor xs ys))) a
    ≡⟨ refl ⟩
  sample ⟦ expr-B n xs ⟧ a
  ∎

otp-game : ∀ (n : Nat)
           (A₁ : CryptoExpr (BitVec n × BitVec n))
           (A₂ : BitVec n → CryptoExpr Bool)
         → CryptoExpr Bool 
otp-game n A₁ A₂ = uniform-expr n >>= λ xs →
                   A₁ >>= λ { (m₁ , m₂) →
                   coin-expr >>= λ b →
                   let msg = bitvec-xor xs (if b then m₁ else m₂)
                   in A₂ msg >>= λ b′ →
                   return (nxor b b′)}

otp-game-unwinnable : ∀ (n : Nat)
                        (A₁ : CryptoExpr (BitVec n × BitVec n))
                        (A₂ : BitVec n → CryptoExpr Bool)
                    → negpow2 1 ≡ sample ⟦ otp-game n A₁ A₂ ⟧ true
otp-game-unwinnable n A₁ A₂ = {!!}

otp-game′ : ∀ (n : Nat)
              (A : BitVec n → CryptoExpr Bool)
          → CryptoExpr Bool
otp-game′ n A = uniform-expr n >>= λ xs →
                coin-expr >>= λ b →
                A xs >>= λ b′ →
                return (nxor b b′)

otp-game′-unwinnable : ∀ (n : Nat)
                         (A : BitVec n → CryptoExpr Bool)
                     → negpow2 1 ≡ sample ⟦ otp-game′ n A ⟧ true
otp-game′-unwinnable n A = {!!}

