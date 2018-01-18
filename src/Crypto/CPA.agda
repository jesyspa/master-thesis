module Crypto.CPA where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Schemes
open import Crypto.Oracle

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
