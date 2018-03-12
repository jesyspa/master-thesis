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
open import Crypto.CPA
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


counterexample-proves-not-forall : ∀{l}{A : Set l}(P : A → Set)
                                 → Σ A (λ a → ¬ P a) → ¬ (∀ a → P a)
counterexample-proves-not-forall P (a , np) u = np (u a)

≡D-counterexample : ∀{A}{{_ : Eq A}}{d₀ d₁ : ListDist A}
                  → (a : A) → ¬(sample d₀ a ≡ sample d₁ a)
                  → ¬(d₀ ≡D d₁)
≡D-counterexample a ce de = ce (sample-invariant de a)

OTP-not-IND-CPA : ∀ n → ¬(n ≡ 0) → Σ (SimpleCPAAdv (OTP n)) (λ A → ¬(coin ≡D ⟦ IND-CPA (OTP n) A ⟧))
OTP-not-IND-CPA n neq = adv , pf
  where
    mgen : CryptoExpr (BitVec n × BitVec n)
    mgen = return (replicate-bv n false , replicate-bv n true) 
    decide : (BitVec n × BitVec n) → (BitVec n → CryptoExpr (BitVec n)) → BitVec n → CryptoExpr Bool
    decide (m₀ , m₁) o ct = fmap (isYes ∘ _==_ ct) (o m₁)
    adv = simple-cpa-adv mgen decide
    pf : ¬ (coin ≡D ⟦ IND-CPA (OTP n) adv ⟧)
    pf = ≡D-counterexample true {!!} 
