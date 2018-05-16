module Interaction.Dependent.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Parametrised.Monad
open import Interaction.Dependent.InteractionStructure 
open import Interaction.Dependent.FreeMonad 

open InteractionStructure
open IxMonad {{...}}
open IxMonadMorphism

module _ {l}(IS : InteractionStructure){S : Set l} where
  record Implementation (M : (S → Set) → S → Set) : Set l where
    field 
      StateI : State IS → S
      ImplI  : {s : State IS}(c : Command IS s) → M (DepAtkey (Response IS c) (StateI ∘′ next IS)) (StateI s)
open Implementation

module _ {l}{IS}{S : Set l}{M : (S → Set) → S → Set}{{_ : IxMonad M}} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M → IxMonadMorphism (FreeMonad IS) M
  StateM (uprop-Impl impl) = StateI impl
  TermM (uprop-Impl impl) (Return-FM a) = returnⁱ a
  TermM (uprop-Impl impl) (Invoke-FM c cont) = ImplI impl c >>=ⁱ λ { (DepV r) → TermM (uprop-Impl impl) (cont r) }

SyntacticImplementation : (IS₁ IS₂ : InteractionStructure) → Set
SyntacticImplementation IS₁ IS₂ = Implementation IS₁ (FreeMonad IS₂)

SynImpl = SyntacticImplementation

module _ {IS : InteractionStructure} where
  id-SI : SynImpl IS IS
  StateI id-SI = id
  ImplI  id-SI c = Invoke-FM c λ r → Return-FM (DepV r)

module _ {IS₁ IS₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂) → IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) 
  fmap-SynImpl-FM = uprop-Impl

module _ {IS₁ IS₂ IS₃ : InteractionStructure} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  StateI (comp-SI si sj) = StateI sj ∘′ StateI si
  ImplI  (comp-SI si sj) = TermM (fmap-SynImpl-FM sj) ∘ fmapⁱ (λ { (DepV r) → DepV r }) ∘ ImplI si

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  _∘′-SI_ = comp-SI

module _ {IS₁ IS₂}(m : ISMorphism IS₁ IS₂) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂
  StateI fmap-IS-SynImpl = StateF 
  -- goal : DepAtkey (Response IS₁ c) (StateI fmap-IS-SynImpl ∘′ next IS₁) (next IS₂ r)
  ImplI  fmap-IS-SynImpl c = Invoke-FM (CommandF c) lem
    where lem : ∀ r → FreeMonad IS₂ (DepAtkey (Response IS₁ c) (StateF ∘′ next IS₁)) (next IS₂ r)
          lem r rewrite sym (nextF r) = Return-FM (DepV (ResponseF r))  

  fmap-IS-FM : FMMorphism IS₁ IS₂
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _{IS₁ JS₁ IS₂ JS₂} where
  binmap-SI : SynImpl IS₁ IS₂ → SynImpl JS₁ JS₂ → SynImpl (BinTensor-IS IS₁ JS₁) (BinTensor-IS IS₂ JS₂)
  StateI (binmap-SI si sj) (s , t) = StateI si s , StateI sj t
  ImplI  (binmap-SI si sj) {s , t} (left  c) = TermM (fmap-IS-FM $ IncL-IS (StateI sj t)) $ fmapⁱ (λ { (DepV x) → DepV x }) $ ImplI si c
  ImplI  (binmap-SI si sj) {s , t} (right c) = TermM (fmap-IS-FM $ IncR-IS (StateI si s)) $ fmapⁱ (λ { (DepV x) → DepV x }) $ ImplI sj c
