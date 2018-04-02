module Interaction.Stateful.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 

open InteractionStructure

Implementation : (IS : InteractionStructure)(M : Set → Set) → Set
Implementation IS M = (c : Command IS) → M (Response IS c)

record ImplMorphism (IS₁ : InteractionStructure)(M₁ : Set → Set)(IS₂ : InteractionStructure)(M₂ : Set → Set) : Set₁ where
  field
    UnderlyingISM   : ISMorphism IS₁ IS₂
  open ISMorphism UnderlyingISM
  field
    InterpretationM : ∀{c} → M₂ (Response IS₂ (CommandF c)) → M₁ (Response IS₁ c)
open ImplMorphism

module _ {IS : InteractionStructure}{M : Set → Set} where
  id-ImplM : ImplMorphism IS M IS M
  UnderlyingISM   id-ImplM = id-IS
  InterpretationM id-ImplM = id

module _ {IS₁ M₁ IS₂ M₂ IS₃ M₃} where
  comp-ImplM : ImplMorphism IS₁ M₁ IS₂ M₂ → ImplMorphism IS₂ M₂ IS₃ M₃ → ImplMorphism IS₁ M₁ IS₃ M₃
  UnderlyingISM   (comp-ImplM m₁ m₂) = comp-IS (UnderlyingISM m₁) (UnderlyingISM m₂)
  InterpretationM (comp-ImplM m₁ m₂) = InterpretationM m₁ ∘′ InterpretationM m₂

module _ {A}(M : Set → Set){ISf : A → InteractionStructure} where
  Match-Impl : (sif : ∀ a → Implementation (ISf a) M) → Implementation (Σ-IS ISf) M
  Match-Impl sif (a  , c) = sif a c

module _ {IS₁ IS₂}(M : Set → Set) where
  BinMatch-Impl : Implementation IS₁ M → Implementation IS₂ M → Implementation (IS₁ ⊎-IS IS₂) M
  BinMatch-Impl si₁ si₂ = Match-Impl M λ { false → si₁ ; true → si₂ }
