{-# OPTIONS --type-in-type #-}
module Synthetic.CryptoExpr ST where

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

open FM CryptoExprCS public using () renaming (FreeMonad to CryptoExpr)
