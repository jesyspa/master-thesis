module Crypto.EAV where

open import ThesisPrelude
open import Crypto.Schemes
open import Crypto.Syntax

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
