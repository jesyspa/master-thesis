module Crypto.EAV where

open import ThesisPrelude
open import Crypto.Schemes
open import Crypto.Syntax
open import Utility.Bool

record EavAdv (E : EncScheme) : Set₁ where
  constructor eav-adv
  open EncScheme E
  field 
    S  : Set
    A₁ : ∀{O} → CryptoExpr O O (S × PT × PT)
    A₂ : ∀{O} → S → CT → CryptoExpr O O Bool

IND-EAV : ∀{O} → (E : EncScheme)(A : EavAdv E) → CryptoExpr O O Bool 
IND-EAV E A 
  = keygen                       >>=ᴵ λ k 
  → A₁                           >>=ᴵ λ { (s , m₀ , m₁) 
  → coin-expr                    >>=ᴵ λ b
  → enc k (if b then m₀ else m₁) >>=ᴵ λ ct
  → A₂ s ct                      >>=ᴵ λ b′ 
  → returnᴵ (nxor b b′) 
  }
  where
    open EncScheme E
    open EavAdv A
