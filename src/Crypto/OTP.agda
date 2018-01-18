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

record EncScheme : Set₁ where
  constructor enc-scheme
  field
    Key PT CT : Set
    
    keygen : CryptoExpr Key
    enc    : Key → PT → CryptoExpr CT
    dec    : Key → CT → PT

    correct : ∀{k pt} → fmap (dec k) (enc k pt) ≡ return pt

OTP : (n : Nat) → EncScheme
OTP n = enc-scheme (BitVec n) 
                   (BitVec n) 
                   (BitVec n) 
                   (uniform-expr n)
                   (λ k pt → return (bitvec-xor k pt) )
                   (λ k ct → bitvec-xor k ct)
                   {!!}

-- We want a "opaque" way of passing S around.
-- The CPAAdv can NOT inspect it!

-- AG: monad state in CPS style?
CE : (S A : Set) → Set
CE = {!!}

record Oracle (In Out S : Set) : Set₁ where
  constructor oracle
  field
    query : In → CE S Out

record EavAdv (E : EncScheme) : Set₁ where
  constructor eav-adv
  open EncScheme E
  field 
    S  : Set
    A₁ : CryptoExpr (S × PT × PT)
    A₂ : S → CT → CryptoExpr Bool
    -- How about asking the adversary to prove that his
    -- message is not the encrypted one? 
    -- ie. defend from bad-events on the type-level!

record CPAAdv (E : EncScheme) : Set₁ where
  constructor eav-adv
  open EncScheme E
  field 
    STₐ  : Set
    A₁ : ∀{σ} → Oracle PT CT σ → CE σ (STₐ × PT × PT)
    A₂ : ∀{σ} → Oracle PT CT σ → STₐ → CT → CE σ Bool
    -- How about asking the adversary to prove that his
    -- message is not the encrypted one? 
    -- ie. defend from bad-events on the type-level!


IND-EAV : (E : EncScheme)(A : EavAdv E) → CryptoExpr Bool 
IND-EAV E A 
  = keygen                       >>= λ k 
  → A₁                           >>= λ { (s , m₀ , m₁) 
  → coin-expr                    >>= λ b
  → enc k (if b then m₀ else m₁) >>= λ ct
  → A₂ s ct                      >>= λ b' 
  → return (isYes (b == b'))
  }
  where
    open EncScheme E
    open EavAdv A

OTP-is-IND-EAV : ∀{n}(A : EavAdv (OTP n))
               → ⟦ IND-EAV (OTP n) A ⟧ ≡D coin
OTP-is-IND-EAV A = {!!}

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

