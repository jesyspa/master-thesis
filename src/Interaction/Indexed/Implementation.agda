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

module _ {S}(IS : IStruct S){𝑺 : Set} where
  record Implementation (M : (𝑺 → Set) → 𝑺 → Set)(StateF : S → 𝑺) : Set where
    field
      RunImpl : {s : S}(c : Command IS s) → M (StrongAtkey (Response IS c) (StateF ∘′ next IS)) (StateF s)

open Implementation

module _ {S}{IS : IStruct S}{𝑺 : Set}{M : (𝑺 → Set) → 𝑺 → Set}{{_ : IxMonad M}}{StateF : S → 𝑺} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M StateF → IxMonadMorphism (FreeMonad IS) M StateF
  RunIxMM (uprop-Impl impl) (Return-FM a) = returnⁱ a
  RunIxMM (uprop-Impl impl) (Invoke-FM c cont) = RunImpl impl c >>=ⁱ λ { (StrongV r refl) → RunIxMM (uprop-Impl impl) (cont r) }

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(StateF : S₁ → S₂) where
  SyntacticImplementation : Set
  SyntacticImplementation = Implementation IS₁ (FreeMonad IS₂) StateF

SynImpl = SyntacticImplementation

module _ {S}{IS : IStruct S} where
  id-SI : SynImpl IS IS id
  RunImpl id-SI c = Invoke-FM c λ r → Return-FM (StrongV r refl)

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : S₁ → S₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂ StateF) → FMMorphism IS₁ IS₂ StateF
  fmap-SynImpl-FM = uprop-Impl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{f g} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ f → SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₃ (g ∘′ f)
  RunImpl (comp-SI si sj) x = RunIxMM (fmap-SynImpl-FM sj) (fmapⁱ (λ { (StrongV r refl) → StrongV r refl }) (RunImpl si x))

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₂ IS₃ g → SynImpl IS₁ IS₂ f → SynImpl IS₁ IS₃ (g ∘′ f)
  _∘′-SI_ = flip comp-SI

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{StateF : S₁ → S₂}(m : ISMorphism IS₁ IS₂ StateF) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂ StateF
  RunImpl fmap-IS-SynImpl c = Invoke-FM (CommandF c) lem
    where lem : ∀ r → FreeMonad IS₂ (StrongAtkey (Response IS₁ c) (StateF ∘′ next IS₁)) (next IS₂ r)
          lem r = Return-FM (StrongV (ResponseF r) (sym (nextF r)))  

  fmap-IS-FM : FMMorphism IS₁ IS₂ StateF
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _ {S₁ S₂ T₁ T₂}
         {IS₁ : IStruct S₁}{IS₂ : IStruct S₂}
         {JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         {StateF₁ : S₁ → T₁}{StateF₂ : S₂ → T₂} where
  binmap-SI : SynImpl IS₁ JS₁ StateF₁ → SynImpl IS₂ JS₂ StateF₂ → SynImpl (BinTensor-IS IS₁ IS₂) (BinTensor-IS JS₁ JS₂) (StateF₁ ***′ StateF₂)
  RunImpl (binmap-SI si sj) {s , t} (left  c)
    = RunIxMM (fmap-IS-FM $ IncL-IS (StateF₂ t)) $ fmapⁱ (λ { (StrongV x refl) → StrongV x refl }) $ RunImpl si c
  RunImpl (binmap-SI si sj) {s , t} (right c)
    = RunIxMM (fmap-IS-FM $ IncR-IS (StateF₁ s)) $ fmapⁱ (λ { (StrongV x refl) → StrongV x refl }) $ RunImpl sj c
