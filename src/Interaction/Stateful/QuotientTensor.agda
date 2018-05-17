module Interaction.Stateful.QuotientTensor where

open import ThesisPrelude
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.Implementation 

open InteractionStructure
open ISMorphism
open Implementation

module _ IS JS where
  record ISEmbedding : Set where
    field
      StateE    : State IS → State JS
      nextE     : ∀{s}{c : Command JS (StateE s)}(r : Response JS c) → State IS
      nextECong : ∀{s}{c : Command JS (StateE s)}(r : Response JS c) → StateE (nextE r) ≡ next JS r

open ISEmbedding

module _ {IS JS}(emb : ISEmbedding IS JS) where
  QuotientTensor-IS : InteractionStructure
  State     QuotientTensor-IS    = State IS
  Command   QuotientTensor-IS  s = Command IS s ⊎ Command JS (StateE emb s)
  Response  QuotientTensor-IS {s} (left  c) = Response IS c
  Response  QuotientTensor-IS {s} (right c) = Response JS c
  next      QuotientTensor-IS {s} {left  c} r = next IS r
  next      QuotientTensor-IS {s} {right c} r = nextE emb r

module _ {IS JS}{emb : ISEmbedding IS JS} where
  QMatch-IS : ∀{KS} → ISMorphism IS KS → ISMorphism JS KS → ISMorphism (QuotientTensor-IS emb) KS
  StateF    (QMatch-IS mi mj) s = StateF mi s
  CommandF  (QMatch-IS mi mj) {s} (left  c) = CommandF mi c
  -- uhoh.  I need a relation between IS -> KS and JS -> KS, in particular that the former factorises
  -- through the latter when it comes to states.
  CommandF  (QMatch-IS mi mj) {s} (right c) = {!CommandF mj c!}
  ResponseF (QMatch-IS mi mj) = {!!}
  nextF     (QMatch-IS mi mj) = {!!}
