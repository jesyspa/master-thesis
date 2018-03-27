module Interaction.Complete.PlayerList where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 
open import Interaction.Complete.Combine 

open InteractionStructure
open ISMorphism
open MethodSig
open PlayerSig

data PlayerList : List InteractionStructure → List PlayerSig → Set₁ where
  Nil-PL : PlayerList [] []
  Cons-PL : ∀{IS ISs sig sigs}
          → PlayerImpl (BinCoproduct-IS IS (Sig2IS (BinUnion*-PS sigs))) sig
          → PlayerList ISs sigs
          → PlayerList (IS ∷ ISs) (sig ∷ sigs)

Combine* : ∀{ISs sigs} → PlayerList ISs sigs → PlayerImpl (BinCoproduct*-IS ISs) (BinUnion*-PS sigs)
Combine* Nil-PL = ImplTrivial-PS Zero-IS 
Combine* (Cons-PL plr plrs) = Combine plr (Combine* plrs)
