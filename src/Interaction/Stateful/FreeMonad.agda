module Interaction.Stateful.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Interaction.Stateful.InteractionStructure 

open InteractionStructure
open ISMorphism

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data FreeMonad (IS : InteractionStructure) : (State IS → Set) → (State IS → Set) where
  Return-FM : ∀{A s} → A s → FreeMonad IS A s 
  Invoke-FM : ∀{A s} → (c : Command IS s) → ((r : Response IS c) → FreeMonad IS A (next IS r)) → FreeMonad IS A s

module _ {IS : InteractionStructure} where
  fmap-FM : ∀{A B s} → (∀{s′} → A s′ → B s′) → FreeMonad IS A s → FreeMonad IS B s
  fmap-FM f (Return-FM a) = Return-FM (f a)
  fmap-FM f (Invoke-FM c cont) = Invoke-FM c (λ r → fmap-FM f (cont r))

  bind-FM : ∀{A B s} → FreeMonad IS A s → (∀{s′} → A s′ → FreeMonad IS B s′) → FreeMonad IS B s
  bind-FM (Return-FM a) fun = fun a
  bind-FM (Invoke-FM c cont) fun = Invoke-FM c λ r → bind-FM (cont r) fun


record FMMorphism (IS₁ IS₂ : InteractionStructure) : Set₁ where
  field
    StateFM : State IS₂ → State IS₁
    ProgFM  : ∀{A s} → FreeMonad IS₁ A (StateFM s) → FreeMonad IS₂ (A ∘′ StateFM) s
open FMMorphism

module _ {IS₁ IS₂}(m : ISMorphism IS₁ IS₂) where
  fmap-IS-FM-switch : ∀{A}{s : State IS₂}{c : Command IS₁ (StateF m s)}(r : Response IS₂ (CommandF m c))
                    → FreeMonad IS₁ A (next IS₁ (ResponseF m r))
                    → FreeMonad IS₁ A (StateF m (next IS₂ r))
  fmap-IS-FM-switch r fm rewrite nextF m r = fm
  
  {-# TERMINATING #-}
  fmap-IS-FM-impl : ∀{A s} → FreeMonad IS₁ A (StateF m s) → FreeMonad IS₂ (A ∘′ StateF m) s
  fmap-IS-FM-impl (Return-FM a) = Return-FM a
  fmap-IS-FM-impl (Invoke-FM {A} c cont) = Invoke-FM (CommandF m c) λ r → fmap-IS-FM-impl (fmap-IS-FM-switch r (cont (ResponseF m r)))

  fmap-IS-FM : FMMorphism IS₁ IS₂
  StateFM fmap-IS-FM = StateF m
  ProgFM  fmap-IS-FM = fmap-IS-FM-impl
