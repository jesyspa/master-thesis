{-# OPTIONS --type-in-type #-}
open import Syntactic.OracleData
module Syntactic.OracleEval (OD : OracleData) where

open OracleData OD

open import ThesisPrelude
open import Syntactic.CryptoExpr
open import Syntactic.CryptoExprHelpers
open import Syntactic.CommandStructure
open FMBegin
open import Syntactic.OracleExpr OD

open OracleExprCmd

record OracleImpl (OST : Set) : Set where
  field
    Impl : OracleInit → CryptoExpr OST ⊤
    Call : OracleArg  → CryptoExpr OST OracleResult

     
embedState-CE : ∀{S T A} → CryptoExpr T A → CryptoExpr (S × T) A
embedState-CE (Return-FM a) = Return-FM a
embedState-CE (Invoke-FM (Uniform n) cont) = Invoke-FM (Uniform n) λ v → embedState-CE (cont v)
embedState-CE (Invoke-FM  GetState cont) = Invoke-FM GetState λ st → embedState-CE (cont (snd st))
embedState-CE (Invoke-FM (SetState st) cont) = modify-CE (second $ const st) >>= λ _ → embedState-CE (cont tt)

module _ {AST : Set}{OST}(impl : OracleImpl OST) where
  open OracleImpl impl
  eval-OI : ∀{A} → CryptoOracleExpr AST A → CryptoExpr (AST × OST) A
  eval-OI (Return-FM a) = Return-FM a
  eval-OI (Invoke-FM (false , Uniform n) cont) = Invoke-FM (Uniform n) λ v → eval-OI (cont v)
  eval-OI (Invoke-FM (false , GetState) cont) = Invoke-FM GetState λ st → eval-OI (cont (fst st))
  eval-OI (Invoke-FM (false , SetState st) cont) = modify-CE (first $ const st) >>= λ st → eval-OI (cont tt)
  eval-OI (Invoke-FM (true  , InitOracle st) cont) = embedState-CE (Impl st) >>= λ _ → eval-OI (cont tt)
  eval-OI (Invoke-FM (true  , CallOracle arg) cont) = embedState-CE (Call arg) >>= λ r → eval-OI (cont r)
