{-# OPTIONS --type-in-type #-}
open import Synthetic.OracleData
module Synthetic.OracleExpr (ST : Set)(OD : OracleData) where

open OracleData OD

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Synthetic.CSConstructs
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition
open import Probability.Class

open CommandStructure

data OracleExprCmd : Set where
  InitOracle : OracleInit → OracleExprCmd
  CallOracle : OracleArg  → OracleExprCmd

OracleExprCS : CommandStructure
Command  OracleExprCS = OracleExprCmd
Response OracleExprCS (InitOracle st)  = ⊤
Response OracleExprCS (CallOracle arg) = OracleResult

open FM OracleExprCS public renaming (FreeMonad to OracleExpr)

initOracle-OE : OracleInit → OracleExpr ⊤
initOracle-OE st = smart-constructor (InitOracle st)

callOracle-OE : OracleArg → OracleExpr OracleResult
callOracle-OE arg = smart-constructor (CallOracle arg)

open FM (bincoproduct-CS CryptoExprCS OracleExprCS) renaming (FreeMonad to CryptoOracleExpr)

uniform-COE : (n : Nat) → CryptoOracleExpr (BitVec n)
uniform-COE n = smart-constructor (false , Uniform n)

coin-COE : CryptoOracleExpr Bool
coin-COE = fmap (λ { (v ∷ []) → v }) (uniform-COE 1)

getState-COE : CryptoOracleExpr ST
getState-COE = smart-constructor (false , GetState)

setState-COE : ST → CryptoOracleExpr ⊤
setState-COE st = smart-constructor (false , SetState st)

initOracle-COE : OracleInit → CryptoOracleExpr ⊤
initOracle-COE st = smart-constructor (true , InitOracle st)

callOracle-COE : OracleArg → CryptoOracleExpr OracleResult
callOracle-COE arg = smart-constructor (true , CallOracle arg)
