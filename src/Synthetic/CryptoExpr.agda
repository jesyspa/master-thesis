{-# OPTIONS --type-in-type #-}
module Synthetic.CryptoExpr where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Utility.Vector.Definition

open CommandStructure

module _ ST where
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

module _ {ST} where
  uniform-CE : (n : Nat) → CryptoExpr ST (BitVec n)
  uniform-CE n = smart-constructor (Uniform n)
  
  coin-CE : CryptoExpr ST Bool
  coin-CE = fmap (λ { (v ∷ []) → v }) (uniform-CE 1)
  
  getState-CE : CryptoExpr ST ST
  getState-CE = smart-constructor GetState 
  
  setState-CE : ST → CryptoExpr ST ⊤
  setState-CE st = smart-constructor (SetState st)

  modify-CE : (ST → ST) → CryptoExpr ST ST
  modify-CE f = do
    st <- getState-CE
    let st′ = f st
    setState-CE st′
    return st′
