module Interaction.Dependent.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Parametrised.Monad
open import Algebra.Parametrised.MonadMorphism
open import Interaction.Dependent.InteractionStructure 
open import Interaction.Dependent.FreeMonad 

open InteractionStructure
open ParMonad {{...}}
open ParMonadMorphism

module _ {l}(IS : InteractionStructure){S : Set l} where
  record Implementation (M : S → S → Set → Set) : Set l where
    field 
      StateI : State IS → S
      ImplI  : {s : State IS}(c : Command IS s) → M (StateI s) (StateI (next IS c)) (Response IS c)
open Implementation

module _ {l}{IS}{S : Set l}{M : S → S → Set → Set}{{_ : ParMonad M}} where
  open ParMonadMorphism
  uprop-Impl : Implementation IS M → ParMonadMorphism (FreeMonad IS) M
  StateM (uprop-Impl impl) = StateI impl
  TermM (uprop-Impl impl) (Return-FM a) = returnᵖ a
  TermM (uprop-Impl impl) (Invoke-FM c cont) = ImplI impl c >>=ᵖ λ r → TermM (uprop-Impl impl) (cont r)

SyntacticImplementation : (IS₁ IS₂ : InteractionStructure) → Set
SyntacticImplementation IS₁ IS₂ = Implementation IS₁ (FreeMonad IS₂)

SynImpl = SyntacticImplementation

module _ {IS : InteractionStructure} where
  id-SI : SynImpl IS IS
  StateI id-SI = id
  ImplI  id-SI c = Invoke-FM c Return-FM

module _ {IS₁ IS₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂) → ParMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) 
  fmap-SynImpl-FM = uprop-Impl

module _ {IS₁ IS₂ IS₃ : InteractionStructure} where
  open ParMonadMorphism
  comp-SI : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  StateI (comp-SI si sj) = StateI sj ∘′ StateI si
  ImplI  (comp-SI si sj) = TermM (fmap-SynImpl-FM sj) ∘ ImplI si

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  _∘′-SI_ = comp-SI

module _ {IS₁ IS₂}(m : ISMorphism IS₁ IS₂) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂
  StateI fmap-IS-SynImpl = StateF 
  ImplI  fmap-IS-SynImpl c rewrite nextF c = Invoke-FM (CommandF c) (Return-FM ∘′ ResponseF)

  fmap-IS-FM : FMMorphism IS₁ IS₂
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _{IS₁ JS₁ IS₂ JS₂} where
  binmap-SI : SynImpl IS₁ IS₂ → SynImpl JS₁ JS₂ → SynImpl (BinTensor-IS IS₁ JS₁) (BinTensor-IS IS₂ JS₂)
  StateI (binmap-SI si sj) (s , t) = StateI si s , StateI sj t
  ImplI  (binmap-SI si sj) {s , t} (left  c) = TermM (fmap-IS-FM $ IncL-IS (StateI sj t)) $ ImplI si c
  ImplI  (binmap-SI si sj) {s , t} (right c) = TermM (fmap-IS-FM $ IncR-IS (StateI si s)) $ ImplI sj c
