module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 

open PlayerDef

module _ {def₁ def₂ : PlayerDef} where
  Combine-FM : (plr : Impl-PD def₂) → FMMorphism (IS-PD (Extend-PD def₁ def₂)) (IS-PD (Join-PD def₁ def₂))
  Combine-FM plr (Return-FM a) = Return-FM a
  Combine-FM plr (Invoke-FM (false , c) cont) = Invoke-FM (false , c) λ r → Combine-FM plr (cont r)
  Combine-FM plr (Invoke-FM (true  , (name , arg)) cont) = bind-FM (fmap-IS-FM (InclR-IS _ _) (plr name arg)) λ r → Combine-FM plr (cont r)

  Combine : Impl-PD (Extend-PD def₁ def₂)
          → Impl-PD def₂
          → Impl-PD (Join-PD def₁ def₂)
  Combine plr₁ plr₂ (false , name) = fmap-MI (Combine-FM plr₂) (plr₁ name)
  Combine plr₁ plr₂ (true  , name) = (fmap-MI ∘′ fmap-IS-FM) (InclR-IS _ _) (plr₂ name)
