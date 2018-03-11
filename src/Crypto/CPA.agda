module Crypto.CPA where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Schemes
open import Crypto.Oracle
open import Utility.Bool

record SimpleCPAAdv (E : EncScheme) : Set₁ where
  constructor simple-cpa-adv
  open EncScheme E
  field 
    A₁ : CryptoExpr (PT × PT)
    A₂ : (PT → CryptoExpr CT) → CT → CryptoExpr Bool

IND-CPA : (E : EncScheme)(A : SimpleCPAAdv E) → CryptoExpr Bool 
IND-CPA E A 
  = keygen                             >>= λ k 
  → A₁                                 >>= λ m
  → coin-expr                          >>= λ b
  → enc k (if b then fst m else snd m) >>= λ ct
  → A₂ (enc k) ct                      >>= λ b′ 
  → return (nxor b b′) 
  where
    open EncScheme E
    open SimpleCPAAdv A
