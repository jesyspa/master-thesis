module Interaction.Simple where

open import ThesisPrelude
open import Algebra.Proposition

record InteractionStructure : Set₁ where
  field
    Command     : Set
    Response    : Command → Set
    nop         : Command
    nopResponse : IsContractible (Response nop)
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    CommandF  : Command IS₁ → Command IS₂
    ResponseF : ∀{c} → Response IS₂ (CommandF c) → Response IS₁ c
    nopComm   : CommandF (nop IS₁) ≡ nop IS₂
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
CommandF  id-IS = id
ResponseF id-IS = id
nopComm   id-IS = refl

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
nopComm   (comp-IS m₁ m₂) rewrite nopComm m₁ | nopComm m₂ = refl 

data FreeMonad (IS : InteractionStructure) : Set → Set where
  Return-FM : ∀{A} → A → FreeMonad IS A
  Invoke-FM : ∀{A}(c : Command IS) → (Response IS c → FreeMonad IS A) → FreeMonad IS A

module _ (IS₁ IS₂ : InteractionStructure) where
  FMMorphism : Set₁
  FMMorphism = ∀{A} → FreeMonad IS₁ A → FreeMonad IS₂ A

  action-FM : ISMorphism IS₁ IS₂ → FMMorphism
  action-FM m (Return-FM a) = Return-FM a
  action-FM m (Invoke-FM c cont) = Invoke-FM (CommandF m c) λ r → action-FM m (cont (ResponseF m r))

