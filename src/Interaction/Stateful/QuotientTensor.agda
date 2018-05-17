module Interaction.Stateful.QuotientTensor where

open import ThesisPrelude
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.Implementation 

open InteractionStructure
open ISMorphism
open Implementation

module _ {IS JS}(impl : SynImpl IS JS) where
  ModuleTensor-IS : InteractionStructure
  State     ModuleTensor-IS    = State IS
  Command   ModuleTensor-IS  s = Command IS s ⊎ Command JS (StateI impl s)
  Response  ModuleTensor-IS {s} (left  c) = Response IS c
  Response  ModuleTensor-IS {s} (right c) = Response JS c
  next      ModuleTensor-IS {s} {left  c} r = next IS r
  -- Oh yeah, this *is* a problem.
  next      ModuleTensor-IS {s} {right c} r = {!!}
