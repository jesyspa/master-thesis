{-# OPTIONS --type-in-type #-}
module Synthetic.CryptoExpr (ST : Set) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Utility.Vector.Definition

open CommandStructure

data CryptoExprCmd : Set where
  Uniform : Nat → CryptoExprCmd
  GetState : CryptoExprCmd
  SetState : ST → CryptoExprCmd

CryptoExprCS : CommandStructure
Command  CryptoExprCS = CryptoExprCmd
Response CryptoExprCS (Uniform n)      = BitVec n
Response CryptoExprCS GetState      = ST
Response CryptoExprCS (SetState st) = ⊤

open FM CryptoExprCS public renaming (FreeMonad to CryptoExpr)

uniform-CE : (n : Nat) → CryptoExpr (BitVec n)
uniform-CE n = smart-constructor (Uniform n)

coin-CE : CryptoExpr Bool
coin-CE = fmap (λ { (v ∷ []) → v }) (uniform-CE 1)

getState-CE : CryptoExpr ST
getState-CE = smart-constructor GetState 

setState-CE : ST → CryptoExpr ⊤
setState-CE st = smart-constructor (SetState st)
