module Interaction.Indexed.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Algebra.Indexed.MonadMorphism
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 

open InteractionStructure
open IxMonad {{...}}
open IxMonadMorphism

module _ {l S}(IS : IStruct S){𝑺 : Set l} where
  Implementation : (M : (𝑺 → Set) → 𝑺 → Set)(StateF : S → 𝑺) → Set
  Implementation M StateF = {s : S}(c : Command IS s) → M (DepAtkey (Response IS c) (StateF ∘′ next IS)) (StateF s)

module _ {l S}{IS : IStruct S}{𝑺 : Set l}{M : (𝑺 → Set) → 𝑺 → Set}{{_ : IxMonad M}}{StateF : S → 𝑺} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M StateF → IxMonadMorphism (FreeMonad IS) M
  StateM (uprop-Impl impl) = StateF
  TermM (uprop-Impl impl) (Return-FM a) = returnⁱ a
  TermM (uprop-Impl impl) (Invoke-FM c cont) = impl c >>=ⁱ λ { (DepV r) → TermM (uprop-Impl impl) (cont r) }

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(StateF : S₁ → S₂) where
  SyntacticImplementation : Set
  SyntacticImplementation = Implementation IS₁ (FreeMonad IS₂) StateF

SynImpl = SyntacticImplementation

module _ {S}{IS : IStruct S} where
  id-SI : SynImpl IS IS id
  id-SI c = Invoke-FM c λ r → Return-FM (DepV r)

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : S₁ → S₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂ StateF) → IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) 
  fmap-SynImpl-FM = uprop-Impl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{f g} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ f → SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₃ (g ∘′ f)
  comp-SI si sj = TermM (fmap-SynImpl-FM sj) ∘ fmapⁱ (λ { (DepV r) → DepV r }) ∘ si

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₂ f → SynImpl IS₁ IS₃ (g ∘′ f)
  _∘′-SI_ = flip comp-SI

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : S₁ → S₂}(m : ISMorphism IS₁ IS₂ StateF) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂ StateF
  -- goal : DepAtkey (Response IS₁ c) (StateF fmap-IS-SynImpl ∘′ next IS₁) (next IS₂ r)
  fmap-IS-SynImpl c = Invoke-FM (CommandF c) lem
    where lem : ∀ r → FreeMonad IS₂ (DepAtkey (Response IS₁ c) (StateF ∘′ next IS₁)) (next IS₂ r)
          lem r rewrite sym (nextF r) = Return-FM (DepV (ResponseF r))  

  fmap-IS-FM : FMMorphism IS₁ IS₂
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _ {S₁ S₂ T₁ T₂}
         {IS₁ : IStruct S₁}{IS₂ : IStruct S₂}
         {JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         {StateF₁ : S₁ → T₁}{StateF₂ : S₂ → T₂} where
  binmap-SI : SynImpl IS₁ JS₁ StateF₁ → SynImpl IS₂ JS₂ StateF₂ → SynImpl (BinTensor-IS IS₁ IS₂) (BinTensor-IS JS₁ JS₂) (StateF₁ ***′ StateF₂)
  binmap-SI si sj {s , t} (left  c) = TermM (fmap-IS-FM $ IncL-IS (StateF₂ t)) $ fmapⁱ (λ { (DepV x) → DepV x }) $ si c
  binmap-SI si sj {s , t} (right c) = TermM (fmap-IS-FM $ IncR-IS (StateF₁ s)) $ fmapⁱ (λ { (DepV x) → DepV x }) $ sj c
