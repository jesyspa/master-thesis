module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Elem 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 

module _ {ISA₁ ISB₁ ISA₂ ISB₂} where
  CombineSynL : SynImpl ISA₁ (ISA₂ ⊎-IS ISB₁)
              → SynImpl ISB₁ ISB₂
              → SynImpl ISA₁ (ISA₂ ⊎-IS ISB₂)
  CombineSynL I₁ I₂ = comp-SynI I₁
                                (BinMatch-SynI (free-SynImpl (InclL-IS _ _))
                                               (comp-SynI I₂ (free-SynImpl (InclR-IS _ _))))


  CombineSyn : SynImpl ISA₁ (ISA₂ ⊎-IS ISB₁)
             → SynImpl ISB₁ ISB₂
             → SynImpl (ISA₁ ⊎-IS ISB₁) (ISA₂ ⊎-IS ISB₂)
  CombineSyn I₁ I₂ = BinMatch-SynI (CombineSynL I₁ I₂)
                                   (comp-SynI I₂ (free-SynImpl (InclR-IS _ _)))

module _ {ISA ISB IST} where
  CombineSynJ : SynImpl ISA (IST ⊎-IS ISB)
              → SynImpl ISB IST
              → SynImpl ISA IST
  CombineSynJ I₁ I₂ = comp-SynI (CombineSynL I₁ I₂) (free-SynImpl (BinMatch-IS _ _ id-IS id-IS))

module _ {ISA ISB ISC ISs} where
  CombineHead : SynImpl ISA (Extend*-IS ISC (ISB ∷ ISs))
              → SynImpl ISB (Extend*-IS ISC ISs)
              → SynImpl ISA (Extend*-IS ISC ISs)
  CombineHead I₁ I₂ = BinMatch-SynI I₂ id-SynI ∘′-SI rearrange ∘′-SI I₁
    where rearrange : SynImpl (Extend*-IS ISC (ISB ∷ ISs)) (ISB ⊎-IS (Extend*-IS ISC ISs) )
          rearrange = free-SynImpl $ Reassoc′-Coproduct-IS ∘′-IS BinJoin-IS Commute-Coproduct-IS id-IS ∘′-IS Reassoc-Coproduct-IS

module _ {ISA ISB ISs} where
  WeakenBy : ∀ ISC → SynImpl ISA (Extend*-IS ISB ISs) → SynImpl ISA (Extend*-IS ISB (ISC ∷ ISs))
  WeakenBy ISC I = BinJoin-SynI id-SynI (free-SynImpl (InclR-IS _ _)) ∘′-SI I

data ImplTelescope : List InteractionStructure → List InteractionStructure → Set₁ where
  Nil-IT  : ImplTelescope [] []
  Cons-IT : ∀{ISA ISAs ISB ISBs}
          → SynImpl ISA (Extend*-IS ISB ISAs)
          → ImplTelescope ISAs ISBs
          → ImplTelescope (ISA ∷ ISAs) (ISB ∷ ISBs)

CombineSyn* : ∀{ISAs ISBs} → ImplTelescope ISAs ISBs → SynImpl (BinCoproduct*-IS ISAs) (BinCoproduct*-IS ISBs)
CombineSyn* Nil-IT              = id-SynI
CombineSyn* (Cons-IT impl tele) = CombineSyn impl (CombineSyn* tele)
