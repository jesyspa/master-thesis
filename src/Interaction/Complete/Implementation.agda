module Interaction.Complete.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 

open InteractionStructure

Implementation : (M : Set → Set)(IS : InteractionStructure) → Set
Implementation M IS = (c : Command IS) → M (Response IS c)

record SyntaxDef : Set₁ where
  constructor syntax-def
  field
    ImplLang : InteractionStructure
    InfcLang : InteractionStructure

SyntacticImplementation : SyntaxDef → Set
SyntacticImplementation (syntax-def IS₁ IS₂) = Implementation (FreeMonad IS₁) IS₂

record ImplMorphism (M₁ : Set → Set)(IS₁ : InteractionStructure)(M₂ : Set → Set)(IS₂ : InteractionStructure) : Set₁ where
  field
    UnderlyingISM   : ISMorphism IS₁ IS₂
  open ISMorphism UnderlyingISM
  field
    InterpretationM : ∀{c} → M₂ (Response IS₂ (CommandF c)) → M₁ (Response IS₁ c)
open ImplMorphism

SyntacticImplMorphism : SyntaxDef → SyntaxDef → Set₁
SyntacticImplMorphism (syntax-def JS₁ IS₁) (syntax-def JS₂ IS₂) = ImplMorphism (FreeMonad JS₁) IS₁ (FreeMonad JS₂) IS₂

module _ {IS₁ IS₂}(M : Set → Set){{_ : Functor M}} where
  fmap-Impl : ISMorphism IS₁ IS₂ → ImplMorphism M IS₁ M IS₂
  UnderlyingISM   (fmap-Impl m) = m
  InterpretationM (fmap-Impl m) mr = fmap ResponseF mr
    where open ISMorphism m

