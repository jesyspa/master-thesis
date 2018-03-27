module Interaction.Complete.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 

open InteractionStructure
open ISMorphism

data FreeMonad (IS : InteractionStructure) : Set → Set where
  Return-FM : ∀{A} → A → FreeMonad IS A
  Invoke-FM : ∀{A} → (c : Command IS) → (Response IS c → FreeMonad IS A) → FreeMonad IS A

module _ {IS : InteractionStructure} where
  bind-FM : ∀{A B} → FreeMonad IS A → (A → FreeMonad IS B) → FreeMonad IS B
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun

FMMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
FMMorphism IS₁ IS₂ = ∀{A} → FreeMonad IS₁ A → FreeMonad IS₂ A

fmap-FM : {IS₁ IS₂ : InteractionStructure} → ISMorphism IS₁ IS₂ → FMMorphism IS₁ IS₂
fmap-FM m (Return-FM a) = Return-FM a
fmap-FM m (Invoke-FM c cont) = Invoke-FM (CommandF m c) λ r → fmap-FM m (cont (ResponseF m r))

