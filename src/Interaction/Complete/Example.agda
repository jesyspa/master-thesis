module Interaction.Complete.Example where

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

data CommandCE : Set where
  uniform : Nat → CommandCE

CE : InteractionStructure
Command  CE = CommandCE
Response CE (uniform n) = BitVec n
  
challengerInfc : InteractionStructure
Command  challengerInfc = ⊤
Response challengerInfc tt = Bool

module _ (K PT CT : Set) where
  data CommandGame : Set where
    keygen : CommandGame
    enc    : K → PT → CommandGame

  encSchemeInfc : InteractionStructure
  Command  encSchemeInfc  = CommandGame
  Response encSchemeInfc keygen     = K
  Response encSchemeInfc (enc k pt) = CT

  data CommandAdv : Set where
    generate-msgs : CommandAdv
    guess-which   : CT → CommandAdv

  adversaryInfc : InteractionStructure
  Command  adversaryInfc = CommandAdv
  Response adversaryInfc generate-msgs   = PT × PT
  Response adversaryInfc (guess-which _) = Bool

  challengerImpl : SynImpl challengerInfc (Extend*-IS CE (encSchemeInfc ∷ adversaryInfc ∷ []))
  challengerImpl tt =
    Invoke-FM (true , false , keygen)                λ k →
    Invoke-FM (true , true , false , generate-msgs)  λ m →
    Invoke-FM (false , uniform 1 )                   λ bv →
    Invoke-FM (true , false , enc k (if head bv
                                     then fst m
                                     else snd m))    λ ct →
    Invoke-FM (true , true , false , guess-which ct) λ b →
    Return-FM (isYes (head bv == b))

  encSchemeImplType : Set
  encSchemeImplType = SynImpl encSchemeInfc (BinCoproduct*-IS $ CE ∷ [])

  adversaryImplType : Set
  adversaryImplType = SynImpl adversaryInfc (BinCoproduct*-IS $ CE ∷ [])
 
  game : encSchemeImplType → adversaryImplType → ISTelescope (challengerInfc ∷ adversaryInfc ∷ CE ∷ [])
  game scheme adv = Cons-IST (CombineSynJ {!challengerImpl!} {!!}) (Cons-IST adv (Cons-IST  Nil-DSIL)

{-
challengerSig : PlayerSig
challengerSig = player-sig ⊤ (const $ method-sig′ ⊤ Bool)

baseChallengerDef : PlayerDef
baseChallengerDef = player-def CE challengerSig 
  
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



-}
