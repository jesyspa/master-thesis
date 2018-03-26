module Interaction.Complete.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition

record InteractionStructure : Set₁ where
  field
    Command     : Set
    Response    : Command → Set
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    CommandF  : Command IS₁ → Command IS₂
    ResponseF : ∀{c} → Response IS₂ (CommandF c) → Response IS₁ c
open ISMorphism

Zero-IS : InteractionStructure
Command  Zero-IS = ⊥
Response Zero-IS ()

init-IS : ∀{IS} → ISMorphism Zero-IS IS
CommandF  init-IS ()
ResponseF init-IS {()}

id-IS : ∀{IS} → ISMorphism IS IS
CommandF  id-IS = id
ResponseF id-IS = id

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂

module _ (IS₁ IS₂ : InteractionStructure) where
  Coproduct-IS : InteractionStructure
  Command  Coproduct-IS = Command IS₁ ⊎ Command IS₂
  Response Coproduct-IS (left  c) = Response IS₁ c
  Response Coproduct-IS (right c) = Response IS₂ c

  Incl-L : ISMorphism IS₁ Coproduct-IS
  CommandF  Incl-L = left
  ResponseF Incl-L = id

  Incl-R : ISMorphism IS₂ Coproduct-IS
  CommandF  Incl-R = right
  ResponseF Incl-R = id

  Match : ∀{IS} → ISMorphism IS₁ IS → ISMorphism IS₂ IS → ISMorphism Coproduct-IS IS
  CommandF  (Match m₁ m₂) (left  c) = CommandF m₁ c
  CommandF  (Match m₁ m₂) (right c) = CommandF m₂ c
  ResponseF (Match m₁ m₂) {left  c} r = ResponseF m₁ r
  ResponseF (Match m₁ m₂) {right c} r = ResponseF m₂ r
