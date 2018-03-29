module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Elem 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 

module _ {ISA₁ ISB₁ ISA₂ ISB₂} where
  CombineSyn : SynImpl ISA₁ (BinCoproduct-IS ISA₂ ISB₁)
             → SynImpl ISB₁ ISB₂
             → SynImpl (BinCoproduct-IS ISA₁ ISB₁) (BinCoproduct-IS ISA₂ ISB₂)
  CombineSyn I₁ I₂ = BinMatch-SynI (comp-SynI I₁ (BinMatch-SynI (free-SynImpl (InclL-IS _ _))
                                                                (comp-SynI I₂ (free-SynImpl (InclR-IS _ _)))))
                                   (comp-SynI I₂ (free-SynImpl (InclR-IS _ _)))

data DepSynImplList : (ISAs ISBs : List InteractionStructure) → Set₁ where
  Nil-DSIL  : DepSynImplList [] []
  Cons-DSIL : ∀{ISA ISB ISAs ISBs}
            → SynImpl ISA (BinCoproduct-IS ISB (BinCoproduct*-IS ISAs))
            → DepSynImplList ISAs ISBs
            → DepSynImplList (ISA ∷ ISAs) (ISB ∷ ISBs)

CombineSyn* : ∀{ISAs ISBs} → DepSynImplList ISAs ISBs → SynImpl (BinCoproduct*-IS ISAs) (BinCoproduct*-IS ISBs)
CombineSyn* Nil-DSIL = id-SynI
CombineSyn* (Cons-DSIL impl dsil) = CombineSyn impl (CombineSyn* dsil) 

