module Interaction.Complete.CryptoExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Combine 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 
open import Utility.Vector

open InteractionStructure
open ISMorphism

data CryptoExprCmd : Set where
  uniform : Nat → CryptoExprCmd

CryptoExpr : InteractionStructure
Command  CryptoExpr = CryptoExprCmd
Response CryptoExpr (uniform n) = BitVec n
  
