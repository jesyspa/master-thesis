module Interaction.Complete.CryptoExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Combine 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 
open import Distribution.Class
open import Utility.Vector

open InteractionStructure
open ISMorphism

data CryptoExprCmd : Set where
  uniform-CE : Nat → CryptoExprCmd

CryptoExpr : InteractionStructure
Command  CryptoExpr = CryptoExprCmd
Response CryptoExpr (uniform-CE n) = BitVec n

joinTelescope : ∀{ISs} → ImplTelescope ISs (replicate (length ISs) CryptoExpr) → SynImpl (BinCoproduct*-IS ISs) CryptoExpr
joinTelescope {ISs} tele = free-SynImpl (Coproduct*-Collapse-IS (length ISs)) ∘′-SI CombineSyn* tele

module _ (M : Set → Set){{DMM : DistMonad M}} where
  open DistMonad DMM
  evalCryptoExpr : Implementation CryptoExpr M
  evalCryptoExpr (uniform-CE n) = uniform n

  evalTelescope : ∀{ISs} → ImplTelescope ISs (replicate (length ISs) CryptoExpr) → Implementation (BinCoproduct*-IS ISs) M
  evalTelescope tele = comp-SynI-Impl (joinTelescope tele) evalCryptoExpr 
