module Interaction.Dependent.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Dependent.InteractionStructure 
open import Algebra.Parametrised.Monad

open InteractionStructure
open ISMorphism

data FreeMonad (IS : InteractionStructure) : State IS → State IS → Set → Set where
  Return-FM : ∀{A s} → A → FreeMonad IS s s A 
  Invoke-FM : ∀{A s₁ s₂} → (c : Command IS s₁) → (Response IS c → FreeMonad IS (next IS c) s₂ A) → FreeMonad IS s₁ s₂ A

module _ {IS : InteractionStructure} where
  fmap-FM : ∀{A B s₁ s₂} → (A → B) → FreeMonad IS s₁ s₂ A → FreeMonad IS s₁ s₂ B
  fmap-FM f (Return-FM a) = Return-FM (f a)
  fmap-FM f (Invoke-FM c cont) = Invoke-FM c (λ r → fmap-FM f (cont r))

  bind-FM : ∀{A B s₁ s₂ s₃} → FreeMonad IS s₁ s₂ A → (A → FreeMonad IS s₂ s₃ B) → FreeMonad IS s₁ s₃ B
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun

module _ {IS : InteractionStructure} where
  open ParMonad
  instance
    FreeParMonadFunctor : ∀{s₁ s₂} → Functor (FreeMonad IS s₁ s₂)
    FreeParMonadFunctor = record { fmap = fmap-FM }

    FreeParMonadMonad : ParMonad (State IS) (FreeMonad IS)
    returnᵖ FreeParMonadMonad = Return-FM
    _>>=ᵖ_  FreeParMonadMonad = bind-FM
    
{-
FMMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
FMMorphism IS₁ IS₂ = ParMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂)

-}
