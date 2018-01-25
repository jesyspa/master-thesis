module Crypto.Schemes where

open import ThesisPrelude
open import Crypto.Syntax

record EncScheme : Set₁ where
  constructor enc-scheme
  field
    Key PT CT : Set
    
    keygen : ∀{O} → CryptoExpr O O Key
    enc    : ∀{O} → Key → PT → CryptoExpr O O CT
    dec    : Key → CT → PT

    correct : ∀{O k pt} → returnCE pt ≡ fmap (dec k) (enc k pt) as CryptoExpr O O PT
