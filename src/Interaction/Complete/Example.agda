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
open MethodSig
open PlayerSig

data CommandCE : Set where
  uniform : Nat → CommandCE

ResponseCE : CommandCE → Set
ResponseCE (uniform n) = BitVec n

CE : InteractionStructure
Command  CE = CommandCE
Response CE = ResponseCE
  
challengerSig : PlayerSig
challengerSig = player-sig ⊤ (const $ method-sig′ ⊤ Bool)

baseChallengerDef : PlayerDef
baseChallengerDef = player-def CE challengerSig 
  
module _ (PT CT : Set) where
  data NamesADV : Set where
    GetMessages : NamesADV
    GetResponse : NamesADV
  
  getMessagesSig : MethodSig
  getMessagesSig = method-sig′ ⊤ (PT × PT)

  getResponseSig : MethodSig
  getResponseSig = method-sig′ CT Bool

  adversarySig : PlayerSig
  MethodName adversarySig = NamesADV
  MethodSigs adversarySig GetMessages = getMessagesSig
  MethodSigs adversarySig GetResponse = getResponseSig

  baseAdversaryDef : PlayerDef
  baseAdversaryDef = player-def CE adversarySig

  challengerDef : PlayerDef 
  challengerDef = Extend*-PD baseChallengerDef (baseAdversaryDef ∷ [])

  challengerImpl : Impl-PD challengerDef
  challengerImpl tt tt = {!!} -- implementation of the game

  adversaryDef : PlayerDef
  adversaryDef = Extend*-PD baseAdversaryDef []

  game-players : Impl-PD adversaryDef → PlayerList (baseChallengerDef ∷ baseAdversaryDef ∷ [])
  game-players adv = Cons-PL challengerImpl (Cons-PL adv Nil-PL)


