module Interaction.Complete.Example where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 
open import Interaction.Complete.Combine 
open import Interaction.Complete.PlayerList 
open import Utility.Vector

open InteractionStructure
open ISMorphism
open Method
open Player

data CommandCE : Set where
  uniform : Nat → CommandCE

ResponseCE : CommandCE → Set
ResponseCE (uniform n) = BitVec n

CE : InteractionStructure
Command  CE = CommandCE
Response CE = ResponseCE
  
