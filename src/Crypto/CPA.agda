module Crypto.CPA where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Schemes
open import Crypto.Oracle

record CPAAdv (E : EncScheme) : Set₁ where
  constructor cpa-adv
  open EncScheme E
  field 
    STₐ  : Set
    A₁ : ∀{O} → Oracle PT CT O → CryptoExpr O O (STₐ × PT × PT)
    A₂ : ∀{O} → Oracle PT CT O → STₐ → CT → CryptoExpr O O Bool
    -- How about asking the adversary to prove that his
    -- message is not the encrypted one? 
    -- ie. defend from bad-events on the type-level!
