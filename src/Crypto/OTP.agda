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

if-lem : ∀{l}{A : Set l}{{_ : Eq A}}(fv tv : A)(b : Bool)
       → ¬(fv ≡ tv) → b ≡ isYes (tv == (if b then tv else fv))
if-lem fv tv false ne with tv == fv
... | yes refl = ⊥-elim (ne refl)
... | no neq = refl
if-lem fv tv true ne with tv == tv
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

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


{-
= keygen                              >>= λ k 
→ A₁                                  >>= λ m
→ coin-expr                           >>= λ b
→ enc k (if b then fst m else snd m)  >>= λ ct
→ A₂ m (enc k) ct                     >>= λ b′ 
→ return (nxor b b′) 

fv, tv : BitVec n
= uniform n                     >>= λ k 
→ coin-expr                     >>= λ b
→ enc k (if b then fv else tv)  >>= λ ct
→ fmap (isYes ∘ _==_ tv) (enc k ct)     >>= λ b′ 
→ return (nxor b b′) 

fv, tv : BitVec n
= uniform n                              >>= λ k 
→ coin-expr                              >>= λ b
→ return (nxor b (isYes (tv == if b then fv else tv)))
-}
