module Crypto.Schemes where

open import ThesisPrelude
open import Crypto.Syntax

record EncScheme : Set₁ where
  constructor enc-scheme
  field
    Key PT CT : Set
    
    keygen : CryptoExpr ⊤ Key
    enc    : CryptoExpr (Key × PT) CT
    dec    : Key → CT → PT

    -- Note that we do not carry around a proof of correctness, since
    -- that only makes sense with respect to a particular valuation.

