module Interaction.Complete.PlayerList where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 
open import Interaction.Complete.Combine 

data PlayerList : List PlayerDef → Set₁ where
  Nil-PL : PlayerList []
  Cons-PL : ∀{def defs}
          → Impl-PD (Extend*-PD def defs)
          → PlayerList defs
          → PlayerList (def ∷ defs)

Combine* : ∀{defs} → PlayerList defs → Impl-PD (Join*-PD defs)
Combine* Nil-PL = ImplTrivial-PD
Combine* (Cons-PL plr plrs) = Combine plr (Combine* plrs)
