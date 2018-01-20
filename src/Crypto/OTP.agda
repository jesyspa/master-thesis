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
open import Crypto.ValuationProps ListDist {{DistMonadListDist}}
open import Crypto.Schemes
open import Crypto.SimpleEAV
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


OTP-is-IND-EAV : ∀{n}(A : SimpleEavAdv (OTP n))
               → coin ≡D ⟦ simple-IND-EAV (OTP n) A ⟧
OTP-is-IND-EAV {n} A = sample-equality λ b →
  sample coin b
    ≡⟨ cong (λ e → sample e b) coin-interpretation ⟩
  sample ⟦ coin-expr ⟧ b
    ≡⟨ flip sample-invariant b
          $ general-irrelevance-interpretation (uniform-expr n) coin-expr ⟩
  sample (
    ⟦ uniform-expr n ⟧ >>= λ xs
  → ⟦ coin-expr      ⟧
  ) b
    ≡⟨ flip sample-invariant b
          $ >>=-D-ext ⟦ uniform-expr n ⟧
                      (λ xs → ⟦ coin-expr ⟧)
                      (λ xs → ⟦ A₂ xs ⟧ >>= const ⟦ coin-expr ⟧)
                      (λ xs → general-irrelevance-interpretation (A₂ xs) coin-expr) ⟩
  sample (
    ⟦ uniform-expr n ⟧ >>= λ xs
  → ⟦ A₂ xs          ⟧ >>= λ b′
  → ⟦ coin-expr      ⟧
  ) b
    ≡⟨ flip sample-invariant b
          $ >>=-D-ext ⟦ uniform-expr n ⟧
                      (λ xs → ⟦ A₂ xs ⟧ >>= λ b′ → ⟦ coin-expr ⟧)
                      (λ xs → ⟦ A₂ xs ⟧ >>= λ b′ → ⟦ coin-expr ⟧ >>= λ b → ⟦ return (nxor b′ b) ⟧)
                      (λ xs → >>=-D-ext ⟦ A₂ xs ⟧
                                      (λ b′ → ⟦ coin-expr ⟧)
                                      (λ b′ → ⟦ coin-expr ⟧ >>= λ b → ⟦ return (nxor b′ b) ⟧)
                                      coin-sample-2-interpretation) ⟩
  sample (
    ⟦ uniform-expr n ⟧ >>= λ xs
  → ⟦ A₂ xs          ⟧ >>= λ b′
  → ⟦ coin-expr      ⟧ >>= λ b
  → ⟦ return (nxor b′ b) ⟧
  ) b
    ≡⟨ flip sample-invariant b
          $ >>=-D-ext ⟦ uniform-expr n ⟧
                       (λ xs → ⟦ A₂ xs ⟧ >>= λ b′ → ⟦ coin-expr ⟧ >>= λ b → ⟦ return (nxor b′ b) ⟧)
                       (λ xs → ⟦ coin-expr ⟧ >>= λ b → ⟦ A₂ xs ⟧ >>= λ b′ → ⟦ return (nxor b′ b) ⟧)
                       (λ xs → independence ⟦ coin-expr ⟧ {! ⟦ A₂ xs ⟧!} λ b′ b → ⟦ return (nxor b′ b) ⟧) ⟩
  sample (
    ⟦ uniform-expr n ⟧ >>= λ ct
  → ⟦ coin-expr ⟧      >>= λ b
  → ⟦ A₂ ct ⟧          >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  ) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ coin-expr ⟧      >>= λ b
  → ⟦ uniform-expr n ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧          >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  ) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ coin-expr ⟧                                    >>= λ b
  → ⟦ if b then uniform-expr n else uniform-expr n ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧                                        >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  ) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ A₁ ⟧                                           >>F= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                                    >>= λ b
  → ⟦ if b then uniform-expr n else uniform-expr n ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧                                        >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ A₁ ⟧                               >>= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                        >>= λ b
  → ⟦ if b
      then fmap (λ k → bitvec-xor k m₀) (uniform-expr n)
      else fmap (λ k → bitvec-xor k m₁) (uniform-expr n)
      ⟧                                  >>= λ ct
  → ⟦ A₂ ct ⟧                            >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ A₁ ⟧                               >>= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                        >>= λ b
  → ⟦ fmap (λ k → bitvec-xor k (if b
                                then m₀
                                else m₁))
           (uniform-expr n)            ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧                            >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ A₁ ⟧                               >>= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                        >>= λ b
  → ⟦ uniform-expr n ⟧                   >>= (λ k
  → ⟦ return (bitvec-xor k (if b
                            then m₀
                            else m₁)) ⟧) >>= λ ct
  → ⟦ A₂ ct ⟧                            >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ A₁ ⟧                              >>= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                       >>= λ b
  → ⟦ uniform-expr n ⟧                  >>= λ k
  → ⟦ return (bitvec-xor k (if b
                            then m₀
                            else m₁)) ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧                           >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample (
    ⟦ uniform-expr n ⟧                               >>= λ k
  → ⟦ A₁ ⟧                                           >>= λ { (m₀ , m₁)
  → ⟦ coin-expr ⟧                                    >>= λ b
  → ⟦ return (bitvec-xor k (if b then m₀ else m₁)) ⟧ >>= λ ct
  → ⟦ A₂ ct ⟧                                        >>= λ b′
  → ⟦ return (nxor b′ b) ⟧
  }) b
    ≡⟨ {!!} ⟩
  sample ⟦ simple-IND-EAV (OTP n) A ⟧ b
  ∎
  where
    open SimpleEavAdv A
    open EncScheme (OTP n)
