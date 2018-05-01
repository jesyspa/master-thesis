module Interaction.Stateful.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 

open InteractionStructure

module _ (IS : InteractionStructure){S : Set} where
  record Implementation (M : (S → Set) → S → Set) : Set where
    field 
      StateI : S → State IS
      -- Aaaaaa why do I do this to myself
      ImplI  : (s : S)(c : Command IS (StateI s)) → M (DepAtkey (Response IS c) {!StateI ∘ next IS!}) {!!}

