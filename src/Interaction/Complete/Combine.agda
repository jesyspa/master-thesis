module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Implementation 

module _ {def₁ def₂ : SyntaxDef} where
  open SyntaxDef
  Combine-FM : SyntacticImplementation (ImplLang JS₂) (InfcLang IS₂)
             → FMMorphism (BinCoproduct-IS (ImplLang JS₁) (InfcLang IS₂)) (BinCoproduct-IS (ImplLang JS₁) (ImplLang JS₂))
  Combine-FM impl (Return-FM a) = Return-FM a
  Combine-FM impl (Invoke-FM (false , c) cont) = Invoke-FM (false , c) λ r → Combine-FM impl (cont r)
  Combine-FM impl (Invoke-FM (true  , c) cont) = bind-FM (fmap-IS-FM (InclR-IS _ _) (impl c)) λ r → Combine-FM impl (cont r)

  Combine : SyntacticImplementation (BinCoproduct-IS JS₁ IS₂) IS₁
          → SyntacticImplementation JS₂ IS₂
          → SyntacticImplementation (BinCoproduct-IS JS₁ JS₂) (BinCoproduct-IS IS₁ IS₂)
  Combine I₁ I₂ (false , c) = Combine-FM I₂ (I₁ c)
  Combine I₁ I₂ (true  , c) = fmap-IS-FM (InclR-IS _ _) (I₂ c)

