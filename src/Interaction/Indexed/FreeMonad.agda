module Interaction.Indexed.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Indexed.InteractionStructure 
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism
open import Utility.BTAll

open InteractionStructure
open ISMorphism

data FreeMonad {S}(IS : IStruct S) : (BTAll′ S → Set) → (BTAll′ S → Set) where
  Return-FM : ∀{A s} → A s → FreeMonad IS A s
  Invoke-FM : ∀{A s} → (c : Command IS s) → ((r : Response IS c) → FreeMonad IS A (next IS c r)) → FreeMonad IS A s

module _ {S}{IS : IStruct S} where
  fmap-FM : ∀{A B s} → (∀{s′} → A s′ → B s′) → FreeMonad IS A s → FreeMonad IS B s
  fmap-FM f (Return-FM a) = Return-FM (f a)
  fmap-FM f (Invoke-FM c cont) = Invoke-FM c (λ r → fmap-FM f (cont r))

  bind-FM : ∀{A B s} → FreeMonad IS A s → (∀{s′} → A s′ → FreeMonad IS B s′) → FreeMonad IS B s
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun

module _ {S}{IS : IStruct S} where
  open IxMonad
  instance
    FreeIxMonad : IxMonad (FreeMonad IS)
    returnⁱ FreeIxMonad = Return-FM
    _>>=ⁱ_  FreeIxMonad = bind-FM
    fmapⁱ   FreeIxMonad = fmap-FM
    
module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(f : BTAll′ S₁ → BTAll′ S₂) where
  FMMorphism : Set₁
  FMMorphism = IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) f

  StrongFMMorphism : Set₁
  StrongFMMorphism = IxStrongMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) f
