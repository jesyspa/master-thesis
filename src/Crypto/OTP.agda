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
open import Distribution.PropsClass ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Crypto.Schemes
open import Crypto.EAV
open import Probability.Class
open DistMonad DistMonadListDist
open DistMonadProps DistMonadPropsListDist
open MonadProps is-monad

OTP : (n : Nat) → EncScheme
OTP n = enc-scheme (BitVec n) 
                   (BitVec n) 
                   (BitVec n) 
                   (uniform-expr n)
                   (λ k pt → return (bitvec-xor k pt) )
                   (λ k ct → bitvec-xor k ct)
                   (λ {k} {pt} → cong return (bitvec-xor-self-inverse k pt))


OTP-is-IND-EAV : ∀{n}(A : EavAdv (OTP n))
               → ⟦ IND-EAV (OTP n) A ⟧ ≡D coin
OTP-is-IND-EAV A = {!!}

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

