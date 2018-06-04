module Interaction.Indexed.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Algebra.Indexed.MonadMorphism
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Utility.BTAll 

open InteractionStructure
open IxMonad {{...}}
open IxMonadMorphism

module _ {S}(IS : IStruct S){𝑺 : Set} where
  Implementation : (M : (𝑺 → Set) → 𝑺 → Set)(StateF : BTAll′ S → 𝑺) → Set
  Implementation M StateF = {s : BTAll′ S}(c : Command IS s) → M (StrongAtkey (Response IS c) (StateF ∘′ next IS c)) (StateF s)

module _ {S}{IS : IStruct S}{𝑺 : Set}{M : (𝑺 → Set) → 𝑺 → Set}{{_ : IxMonad M}}{StateF : BTAll′ S → 𝑺} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M StateF → IxMonadMorphism (FreeMonad IS) M
  StateM (uprop-Impl impl) = StateF
  TermM (uprop-Impl impl) (Return-FM a) = returnⁱ a
  TermM (uprop-Impl impl) (Invoke-FM c cont) = impl c >>=ⁱ λ { (StrongV r refl) → TermM (uprop-Impl impl) (cont r) }

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(StateF : BTAll′ S₁ → BTAll′ S₂) where
  SyntacticImplementation : Set
  SyntacticImplementation = Implementation IS₁ (FreeMonad IS₂) StateF

SynImpl = SyntacticImplementation

module _ {S}{IS : IStruct S} where
  id-SI : SynImpl IS IS id
  id-SI c = Invoke-FM c λ r → Return-FM (StrongV r refl)

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : BTAll′ S₁ → BTAll′ S₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂ StateF) → IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) 
  fmap-SynImpl-FM = uprop-Impl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{f g} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ f → SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₃ (g ∘′ f)
  comp-SI si sj x = TermM (fmap-SynImpl-FM sj) (fmapⁱ (λ { (StrongV r refl) → StrongV r refl }) (si x))

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₂ f → SynImpl IS₁ IS₃ (g ∘′ f)
  _∘′-SI_ = flip comp-SI

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : BTAll′ S₁ → BTAll′ S₂}(m : ISMorphism IS₁ IS₂ StateF) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂ StateF
  fmap-IS-SynImpl c = Invoke-FM (CommandF c) lem
    where lem : ∀ r → FreeMonad IS₂ (StrongAtkey (Response IS₁ c) (StateF ∘′ next IS₁ c)) (next IS₂ _ r)
          lem r = Return-FM (StrongV (ResponseF r) (sym (nextF r)))  

  fmap-IS-FM : FMMorphism IS₁ IS₂
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _ {S₁ S₂ T₁ T₂}
         {IS₁ : IStruct S₁}{IS₂ : IStruct S₂}
         {JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         {StateF₁ : BTAll′ S₁ → BTAll′ T₁}{StateF₂ : BTAll′ S₂ → BTAll′ T₂} where
  binmap-SI : SynImpl IS₁ JS₁ StateF₁ → SynImpl IS₂ JS₂ StateF₂ → SynImpl (BinTensor-IS IS₁ IS₂) (BinTensor-IS JS₁ JS₂) (StateF₁ ***-BT′ StateF₂)
  binmap-SI si sj {s ▵ t} (left  c) = TermM (fmap-IS-FM $ IncL-IS (StateF₂ t)) $ fmapⁱ (λ { (StrongV x refl) → StrongV x refl }) $ si c
  binmap-SI si sj {s ▵ t} (right c) = TermM (fmap-IS-FM $ IncR-IS (StateF₁ s)) $ fmapⁱ (λ { (StrongV x refl) → StrongV x refl }) $ sj c
