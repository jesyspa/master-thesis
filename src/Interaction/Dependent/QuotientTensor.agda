module Interaction.Dependent.QuotientTensor where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Parametrised.Monad
open import Algebra.Parametrised.MonadMorphism
open import Interaction.Dependent.InteractionStructure 
open import Interaction.Dependent.FreeMonad 
open import Interaction.Dependent.Implementation 

open InteractionStructure
open ISMorphism
open Implementation

-- This kind of lift-next idea may work, except we also need a proof it commutes with next.
module _ {IS JS}(impl : SynImpl IS JS)(lift-next : ∀ si → (c : Command JS (StateI impl si)) → State IS) where
  QuotientTensor-IS : InteractionStructure
  State     QuotientTensor-IS = State IS
  Command   QuotientTensor-IS  s  = Command IS s ⊎ Command JS (StateI impl s)
  Response  QuotientTensor-IS {s} (left  c) = Response IS c
  Response  QuotientTensor-IS {s} (right c) = Response JS c
  next      QuotientTensor-IS {s} (left  c) = next IS c
  next      QuotientTensor-IS {s} (right c) = lift-next s c
