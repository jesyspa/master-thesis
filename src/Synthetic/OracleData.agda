module Synthetic.OracleData where

open import ThesisPrelude

record OracleData : Set₁ where
  field
    OracleInit   : Set
    OracleArg    : Set
    OracleResult : Set
