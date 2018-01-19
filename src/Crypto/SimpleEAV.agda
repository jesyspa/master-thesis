module Crypto.SimpleEAV where

open import ThesisPrelude
open import Crypto.Schemes
open import Crypto.Syntax
open import Utility.Bool

record SimpleEavAdv (E : EncScheme) : Set₁ where
  constructor simple-eav-adv
  open EncScheme E
  field 
    A₁ : CryptoExpr (PT × PT)
    A₂ : CT → CryptoExpr Bool
    -- How about asking the adversary to prove that his
    -- message is not the encrypted one? 
    -- ie. defend from bad-events on the type-level!


simple-IND-EAV : (E : EncScheme)(A : SimpleEavAdv E) → CryptoExpr Bool 
simple-IND-EAV E A 
  = keygen                       >>= λ k 
  → A₁                           >>= λ { (m₀ , m₁) 
  → coin-expr                    >>= λ b
  → enc k (if b then m₀ else m₁) >>= λ ct
  → A₂ ct                        >>= λ b′ 
  → return (nxor b b′) 
  }
  where
    open EncScheme E
    open SimpleEavAdv A
