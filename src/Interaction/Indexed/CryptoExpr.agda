module Interaction.Indexed.CryptoExpr where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Proposition
open import Algebra.Indexed.Atkey
open import Algebra.Unit
open import Distribution.Class
open import Utility.Vector
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Interaction.Indexed.Implementation 
open import Interaction.Indexed.Joinable 
open import Interaction.Indexed.StateExpr 
open import Interaction.Indexed.DistExpr 

open InteractionStructure
open ISMorphism
open Joinable
open Implementation

crypto-iso : StateExprState ↔ StateExprState × ⊤
crypto-iso = (λ z → z , tt) , fst , (λ a → refl) , λ { (z , tt) → refl }

CryptoExprIS : IStruct (StateExprState × ⊤)
CryptoExprIS = StateExprIS ⊕-IS DistExprIS

joinable-SCE-IS : Joinable CryptoExprIS
joinable-SCE-IS = join-joinable-IS joinable-SE-IS joinable-DE-IS 
