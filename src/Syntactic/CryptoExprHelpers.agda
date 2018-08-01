{-# OPTIONS --type-in-type #-}
module Syntactic.CryptoExprHelpers {ST} where

open import ThesisPrelude
open import Syntactic.Enumeration
open import Syntactic.CommandStructure
open import Syntactic.CryptoExpr ST
open import Utility.Vector.Definition

open CommandStructure

uniform-CE : (n : Nat) → CryptoExpr (BitVec n)
uniform-CE n = smart-constructor (Uniform n)

coin-CE : CryptoExpr Bool
coin-CE = fmap (λ { (v ∷ []) → v }) (uniform-CE 1)

getState-CE : CryptoExpr ST
getState-CE = smart-constructor GetState 

setState-CE : ST → CryptoExpr ⊤
setState-CE st = smart-constructor (SetState st)

modify-CE : (ST → ST) → CryptoExpr ST
modify-CE f = do
  st <- getState-CE
  let st′ = f st
  setState-CE st′
  return st′
