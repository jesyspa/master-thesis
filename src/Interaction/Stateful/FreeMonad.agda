module Interaction.Stateful.FreeMonad where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Stateful.InteractionStructure 
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism

open InteractionStructure
open ISMorphism

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s

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

module _ {IS : InteractionStructure} where
  open IxMonad
  instance
    FreeIxMonad : IxMonad (FreeMonad IS)
    returnⁱ FreeIxMonad = Return-FM
    _>>=ⁱ_ FreeIxMonad  = bind-FM
    fmapⁱ FreeIxMonad   = fmap-FM
    
FMMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
FMMorphism IS₁ IS₂ = IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂)
