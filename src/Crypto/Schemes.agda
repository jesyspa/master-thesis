module Crypto.Schemes where

open import ThesisPrelude
open import Crypto.Syntax

record EncScheme : Set₁ where
  constructor enc-scheme
  field
    Key PT CT : Set
    
    keygen : CryptoExpr Key
    enc    : Key → PT → CryptoExpr CT
    dec    : Key → CT → PT

    correct : ∀{k pt} → return pt ≡ fmap (dec k) (enc k pt)
