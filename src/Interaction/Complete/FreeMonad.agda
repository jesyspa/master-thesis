module Interaction.Complete.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Interaction.Complete.InteractionStructure 

open InteractionStructure
open ISMorphism

data FreeMonad (IS : InteractionStructure) : Set → Set where
  Return-FM : ∀{A} → A → FreeMonad IS A
  Invoke-FM : ∀{A} → (c : Command IS) → (Response IS c → FreeMonad IS A) → FreeMonad IS A

module _ {IS : InteractionStructure} where
  fmap-FM : ∀{A B} → (A → B) → FreeMonad IS A → FreeMonad IS B
  fmap-FM f (Return-FM a) = Return-FM (f a)
  fmap-FM f (Invoke-FM c cont) = Invoke-FM c (λ r → fmap-FM f (cont r))

  pure-FM : ∀{A} → A → FreeMonad IS A
  pure-FM = Return-FM

  ap-FM : ∀{A B} → FreeMonad IS (A → B) → FreeMonad IS A → FreeMonad IS B
  ap-FM (Return-FM f) fa = fmap-FM f fa
  ap-FM (Invoke-FM c cont) fa = Invoke-FM c λ r → ap-FM (cont r) fa

  bind-FM : ∀{A B} → FreeMonad IS A → (A → FreeMonad IS B) → FreeMonad IS B
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun

  instance
    FunctorFreeMonad : Functor (FreeMonad IS)
    FunctorFreeMonad = record { fmap = fmap-FM }
  
    ApplicativeFreeMonad : Applicative (FreeMonad IS)
    ApplicativeFreeMonad = record { pure = pure-FM ; _<*>_ = ap-FM }

    MonadFreeMonad : Monad (FreeMonad IS)
    MonadFreeMonad = record { _>>=_ = bind-FM }

FMMorphism : ∀ IS₁ IS₂ → Set₁
FMMorphism IS₁ IS₂ = ∀{A} → FreeMonad IS₁ A → FreeMonad IS₂ A

fmap-IS-FM : ∀{IS₁ IS₂} → ISMorphism IS₁ IS₂ → FMMorphism IS₁ IS₂
fmap-IS-FM m (Return-FM a) = Return-FM a
fmap-IS-FM m (Invoke-FM c cont) = Invoke-FM (CommandF m c) λ r → fmap-IS-FM m (cont (ResponseF m r))

