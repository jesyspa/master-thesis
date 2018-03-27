module Interaction.Complete.PlayerList where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 
open import Interaction.Complete.Combine 

open InteractionStructure
open ISMorphism
open Method
open Player

mutual
  data PlayerList : List InteractionStructure → Set₁ where
    Nil-PL : PlayerList []
    Cons-PL : ∀{IS ISs}(plrs : PlayerList ISs)(plr : Player (Augment (Combine* plrs) IS)) → PlayerList (IS ∷ ISs)

  Combine* : ∀{ISs} → PlayerList ISs → Player (Coproduct*-IS ISs)
  Combine* Nil-PL = EmptyPlayer
  Combine* (Cons-PL plrs plr) = Combine (Combine* plrs) plr
