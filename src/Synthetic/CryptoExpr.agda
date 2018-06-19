{-# OPTIONS --type-in-type #-}
open import Synthetic.CryptoState
module Synthetic.CryptoExpr (CS : CryptoState) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Utility.Vector.Definition
open import Probability.Class

open CommandStructure
open CryptoState CS

data CryptoExprCmd : Set where
  Uniform : Nat → CryptoExprCmd
  GetAdvState : CryptoExprCmd
  SetAdvState : AdvState → CryptoExprCmd
  InitOracle : OracleInit → CryptoExprCmd
  CallOracle : OracleArg → CryptoExprCmd

CryptoExprCS : CommandStructure
Command  CryptoExprCS = CryptoExprCmd
Response CryptoExprCS (Uniform n)      = BitVec n
Response CryptoExprCS GetAdvState      = AdvState
Response CryptoExprCS (SetAdvState st) = ⊤
Response CryptoExprCS (InitOracle st)  = ⊤
Response CryptoExprCS (CallOracle arg) = OracleResult

open FM CryptoExprCS

CryptoExpr : Set → Set
CryptoExpr A = FreeMonad A

uniform-CE : (n : Nat) → CryptoExpr (BitVec n)
uniform-CE n = smart-constructor (Uniform n)

coin-CE : CryptoExpr Bool
coin-CE = fmap (λ { (v ∷ []) → v }) (uniform-CE 1)

getAdvState-CE : CryptoExpr AdvState
getAdvState-CE = smart-constructor GetAdvState 

setAdvState-CE : AdvState → CryptoExpr ⊤
setAdvState-CE st = smart-constructor (SetAdvState st)

initOracle-CE : OracleInit → CryptoExpr ⊤
initOracle-CE st = smart-constructor (InitOracle st)

callOracle-CE : OracleArg → CryptoExpr OracleResult
callOracle-CE arg = smart-constructor (CallOracle arg)



