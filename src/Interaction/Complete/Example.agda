module Interaction.Complete.Example where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Combine 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 
open import Interaction.Complete.CryptoExpr 
open import Utility.Vector

open InteractionStructure
open ISMorphism

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

  challengerImpl : SynImpl challengerInfc (Extend*-IS CryptoExpr (encSchemeInfc ∷ adversaryInfc ∷ []))
  challengerImpl tt =
    Invoke-FM (true , false , keygen)                λ k →
    Invoke-FM (true , true , false , generate-msgs)  λ m →
    Invoke-FM (false , uniform-CE 1)                 λ bv →
    Invoke-FM (true , false , enc k (if head bv
                                     then fst m
                                     else snd m))    λ ct →
    Invoke-FM (true , true , false , guess-which ct) λ b →
    Return-FM (isYes (head bv == b))

  encSchemeImplType : Set
  encSchemeImplType = SynImpl encSchemeInfc (Extend*-IS CryptoExpr [])

  adversaryImplType : Set
  adversaryImplType = SynImpl adversaryInfc (Extend*-IS CryptoExpr [])

  bindEncScheme : encSchemeImplType → SynImpl challengerInfc (Extend*-IS CryptoExpr [ adversaryInfc ])
  bindEncScheme scheme = CombineHead {_} {_} {_} {[ adversaryInfc ]} challengerImpl (WeakenBy {_} {_} {[]} adversaryInfc scheme)
 
  game : encSchemeImplType → adversaryImplType → ImplTelescope (challengerInfc ∷ adversaryInfc ∷ []) (CryptoExpr ∷ CryptoExpr ∷ [])
  game scheme adv = Cons-IT (bindEncScheme scheme) (Cons-IT adv Nil-IT)


  game′ : encSchemeImplType → adversaryImplType → SynImpl challengerInfc CryptoExpr
  game′ scheme adv = free-SynImpl (BinMatch-IS _ _ id-IS Coproduct-RightUnit-IS) ∘′-SI CombineSyn* (game scheme adv) ∘′-SI free-SynImpl (InclL-IS _ _)
