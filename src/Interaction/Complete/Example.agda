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

module _ (K PT CT : Set) where
  data ChallengerCmd : Set where
    keygen : ChallengerCmd
    enc    : K → PT → ChallengerCmd

  challengerInfc : InteractionStructure
  Command  challengerInfc  = ChallengerCmd
  Response challengerInfc keygen     = K
  Response challengerInfc (enc k pt) = CT

  data AdversaryCmd : Set where
    generate-msgs : AdversaryCmd
    guess-which   : CT → AdversaryCmd

  adversaryInfc : InteractionStructure
  Command  adversaryInfc = AdversaryCmd
  Response adversaryInfc generate-msgs   = PT × PT
  Response adversaryInfc (guess-which _) = Bool

  gameImpl : SynImpl (GameIS Bool) (Extend*-IS CryptoExprIS (challengerInfc ∷ adversaryInfc ∷ []))
  gameImpl tt =
    Invoke-FM (true , false , keygen)                λ k →
    Invoke-FM (true , true , false , generate-msgs)  λ m →
    Invoke-FM (false , uniform-CE 1)                 λ bv →
    Invoke-FM (true , false , enc k (if head bv
                                     then fst m
                                     else snd m))    λ ct →
    Invoke-FM (true , true , false , guess-which ct) λ b →
    Return-FM (isYes (head bv == b))

{-
  encSchemeImplType : Set
  encSchemeImplType = SynImpl encSchemeInfc (Extend*-IS CE [])

  adversaryImplType : Set
  adversaryImplType = SynImpl adversaryInfc (Extend*-IS CE [])

  bindEncScheme : encSchemeImplType → SynImpl challengerInfc (Extend*-IS CE [ adversaryInfc ])
  bindEncScheme scheme = CombineHead {challengerInfc} {encSchemeInfc} {CE} {[ adversaryInfc ]} challengerImpl (WeakenBy {encSchemeInfc} {CE} {[]} adversaryInfc scheme)
 
  game : encSchemeImplType → adversaryImplType → ImplTelescope (challengerInfc ∷ adversaryInfc ∷ []) (CE ∷ CE ∷ [])
  game scheme adv = Cons-IT (bindEncScheme scheme) (Cons-IT adv Nil-IT)


  game′ : encSchemeImplType → adversaryImplType → SynImpl challengerInfc CE
  game′ scheme adv = free-SynImpl (BinMatch-IS _ _ id-IS Coproduct-RightUnit-IS) ∘′-SI CombineSyn* (game scheme adv) ∘′-SI free-SynImpl (InclL-IS _ _)

-}
