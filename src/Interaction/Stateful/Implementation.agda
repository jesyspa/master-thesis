module Interaction.Stateful.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 

open InteractionStructure

module _ {l}(IS : InteractionStructure){S : Set l} where
  record Implementation (M : (S → Set) → S → Set) : Set l where
    field 
      StateI : S → State IS
      ImplI  : (s : S)(c : Command IS (StateI s)) → M (Atkey (Response IS c) s) s

