module Interaction.Fibered.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Fibered.InteractionStructure 
open import Algebra.Fibered.Monad
open import Algebra.Fibered.FunctorMorphism
open import Algebra.Fibered.FiberedSet
open import Utility.BTAll

open InteractionStructure
open ISMorphism

module _ {S}(IS : IStruct S) where
  data FreeMonadCarrier (A : Set)(f : A → BTAll′ S) : Set where
    Return-FMC : A → FreeMonadCarrier A f
    Invoke-FMC : (c : Command IS) → {!!} → FreeMonadCarrier A f
  
  FreeMonad : FiberedSet (BTAll′ S) → FiberedSet (BTAll′ S)
  FreeMonad (A , f) = {!!} , {!!}
  
{-
  Return-FM : ∀{A s} → A s → FreeMonad IS A s
  Invoke-FM : ∀{A s} → (c : Command IS s) → ((r : Response IS c) → FreeMonad IS A (next IS c r)) → FreeMonad IS A s
  -}

{-
module _ {S}{IS : IStruct S} where
  fmap-FM : ∀{A B s} → (∀{s′} → A s′ → B s′) → FreeMonad IS A s → FreeMonad IS B s
  fmap-FM f (Return-FM a) = Return-FM (f a)
  fmap-FM f (Invoke-FM c cont) = Invoke-FM c (λ r → fmap-FM f (cont r))

  bind-FM : ∀{A B s} → FreeMonad IS A s → (∀{s′} → A s′ → FreeMonad IS B s′) → FreeMonad IS B s
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun
  -}

{-
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

-}
