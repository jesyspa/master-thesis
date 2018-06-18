module Synthetic.CryptoState where

open import ThesisPrelude

record CryptoState : Set₁ where
  field
    AdvState     : Set
    OracleInit   : Set
    OracleArg    : Set
    OracleResult : Set
