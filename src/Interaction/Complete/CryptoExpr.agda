module Interaction.Complete.CryptoExpr  where

open import ThesisPrelude
open import Utility.Vector
open import Interaction.Complete.InteractionStructure

data CryptoExprCmd : Set where
  uniform-CE : Nat → CryptoExprCmd

CryptoExprResp : CryptoExprCmd → Set
CryptoExprResp (uniform-CE n) = BitVec n

open InteractionStructure
CryptoExprIS : InteractionStructure
Command  CryptoExprIS = CryptoExprCmd
Response CryptoExprIS = CryptoExprResp

