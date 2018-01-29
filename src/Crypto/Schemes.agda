module Crypto.Schemes where

open import ThesisPrelude
open import Crypto.Syntax

record EncScheme : Set₁ where
  constructor enc-scheme
  field
    Key PT CT : Set
    
    keygen : ∀{O} → CryptoExpr O O ⊤ Key
    enc    : ∀{O} → CryptoExpr O O (Key × PT) CT
    dec    : Key → CT → PT

    -- Note that we do not carry around a proof of correctness, since
    -- that only makes sense with respect to a particular valuation.

