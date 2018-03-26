module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 

open InteractionStructure
open ISMorphism
open Method
open Player

module _ {IS₁ IS₂ : InteractionStructure} where
  Combine-FM : (plr₁ : Player IS₁) → FMMorphism (Augment plr₁ IS₂) (Coproduct-IS IS₁ IS₂)
  Combine-FM plr₁ (Return-FM a)                      = Return-FM a
  Combine-FM plr₁ (Invoke-FM (left  c        ) cont) = Invoke-FM (right c) λ r → Combine-FM plr₁ (cont r)
  Combine-FM plr₁ (Invoke-FM (right (n , arg)) cont) = bind-FM (Impl (Method-fmap (Incl-L IS₁ IS₂) (MethodImpl plr₁ n)) arg) λ r → Combine-FM plr₁ (cont r)

  Combine-Impl : (plr₁ : Player IS₁) → Method (Augment plr₁ IS₂) → Method (Coproduct-IS IS₁ IS₂) 
  Argument (Combine-Impl plr₁ mth)     = Argument mth
  Result   (Combine-Impl plr₁ mth) arg = Result mth arg
  Impl     (Combine-Impl plr₁ mth) arg = Combine-FM plr₁ (Impl mth arg)

  Combine : (plr₁ : Player IS₁)(plr₂ : Player (Augment plr₁ IS₂)) → Player (Coproduct-IS IS₁ IS₂)
  MethodName (Combine plr₁ plr₂) = MethodName plr₁ ⊎ MethodName plr₂
  MethodImpl (Combine plr₁ plr₂) (left  n) = Method-fmap (Incl-L IS₁ IS₂) (MethodImpl plr₁ n)
  MethodImpl (Combine plr₁ plr₂) (right n) = Combine-Impl plr₁ (MethodImpl plr₂ n)
