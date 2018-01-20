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
open import Distribution.Reasoning ListDist {{DistMonadListDist}}
open import Algebra.MonadProps ListDist
open import Crypto.Valuation ListDist {{DistMonadListDist}}
open import Crypto.ValuationProps ListDist {{DistMonadListDist}}
open import Crypto.Schemes
open import Crypto.Reasoning ListDist {{DistMonadListDist}}
open import Crypto.CoinExamples ListDist {{DistMonadListDist}}
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
OTP-is-IND-EAV {n} A =
  coin
    ≡D⟨ coin-interpretation ⟩ˡ
  ⟦ coin-expr ⟧
    ≡D⟨ irrelevance-interpretation (uniform-expr n) coin-expr ⟩
  ⟦( uniform-expr n  >>= λ ct
   → coin-expr )⟧
    ≡D⟨ cong->>= (uniform-expr n)
                 (λ ct → coin-expr)
                 (λ ct → A₂ ct >>= const coin-expr)
                 (λ ct → irrelevance-interpretation (A₂ ct) coin-expr) ⟩
  ⟦( uniform-expr n >>= λ ct
   → A₂ ct          >>= λ b′
   → coin-expr      )⟧
    ≡D⟨ (let expr : (Bool → CryptoExpr Bool) → (BitVec n) → CryptoExpr Bool
             expr f ct = A₂ ct >>= f in
         cong->>= (uniform-expr n)
                  (expr (const coin-expr))
                  (expr (λ b′ → coin-expr >>= λ b → return (nxor b′ b)))
                  (λ ct → cong->>= (A₂ ct)
                                   (const coin-expr)
                                   (λ b′ → coin-expr >>= λ b → return (nxor b′ b))
                                   coin-sample-2)) ⟩
  ⟦( uniform-expr n >>= λ ct
   → A₂ ct          >>= λ b′
   → coin-expr      >>= λ b
   → return (nxor b′ b) )⟧
    ≡D⟨ cong->>= (uniform-expr n)
                 (λ ct → A₂ ct >>= λ b′ → coin-expr >>= λ b → return (nxor b′ b))
                 (λ ct → coin-expr >>= λ b → A₂ ct >>= λ b′ → return (nxor b′ b))
                 (λ ct → interchange-interpretation (A₂ ct) coin-expr (λ b′ b → return (nxor b′ b))) ⟩
  ⟦( uniform-expr n   >>= λ ct
   → coin-expr        >>= λ b
   → A₂ ct            >>= λ b′
   → return (nxor b′ b) )⟧
    ≡D⟨ interchange-interpretation (uniform-expr n) coin-expr
           (λ ct b → A₂ ct >>= λ b′ → return (nxor b′ b)) ⟩
  ⟦( coin-expr      >>= λ b
   → uniform-expr n >>= λ ct
   → A₂ ct          >>= λ b′
   → return (nxor b′ b) )⟧
    ≡D⟨ (let expr : (Bool → CryptoExpr (BitVec n)) → Bool → CryptoExpr Bool
             expr f b = f b >>= λ ct → A₂ ct >>= λ b′ → return (nxor b′ b) in
         cong->>= coin-expr
                  (expr (const (uniform-expr n)))
                  (expr λ b → if b then uniform-expr n else uniform-expr n)
                  (λ b → {!!})) ⟩
  ⟦( coin-expr                                      >>= λ b
   → (if b then uniform-expr n else uniform-expr n) >>= λ ct
   → A₂ ct                                          >>= λ b′
   → return (nxor b′ b) )⟧
    ≡D⟨ irrelevance-interpretation A₁
          ( coin-expr                                      >>= λ b
          → (if b then uniform-expr n else uniform-expr n) >>= λ ct
          → A₂ ct                                          >>= λ b′
          → return (nxor b′ b)) ⟩
  ⟦( A₁                                             >>= const (
     coin-expr                                      >>= λ b
   → (if b then uniform-expr n else uniform-expr n) >>= λ ct
   → A₂ ct                                          >>= λ b′
   → return (nxor b′ b) ))⟧
    ≡D⟨ {!!} ⟩
   {-
    ≡D⟨ cong->>=ˡ A₁
                  (const (coin-expr                                     >>= λ b
                  → (if b then uniform-expr n else uniform-expr n) >>= λ ct
                  → A₂ ct                                          >>= λ b′
                  → return (nxor b′ b) ))
                   (λ { (m₀ , m₁) → coin-expr                                     >>= λ b
                  → (if b then uniform-expr n else uniform-expr n) >>= λ ct
                  → A₂ ct                                          >>= λ b′
                  → return (nxor b′ b)})
                   (λ { (m₀ , m₁) → ?}) ⟩ˡ
                   -}
  ⟦( A₁                                             >>= λ { (m₀ , m₁)
   → coin-expr                                      >>= λ b
   → (if b then uniform-expr n else uniform-expr n) >>= λ ct
   → A₂ ct                                          >>= λ b′
   → return (nxor b′ b) })⟧
    ≡D⟨ {!!} ⟩
  {!!}
  ∎D
  where
    open SimpleEavAdv A
    open EncScheme (OTP n)
                      {-
  ) b
    ≡⟨ {!!} ⟩
  sample (
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

-}
