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

data ISTelescope : List InteractionStructure → Set₁ where
  Base-IST  : ∀{IS} → ISTelescope [ IS ]
  Cons-IST : ∀{IS ISs}
           → SynImpl IS (BinCoproduct*-IS ISs)
           → ISTelescope ISs
           → ISTelescope (IS ∷ ISs)

First*-IS : List InteractionStructure → InteractionStructure
First*-IS = foldr const ⊥-IS

Last*-IS : List InteractionStructure → InteractionStructure
Last*-IS (x ∷ y ∷ ys) = Last*-IS (y ∷ ys)
Last*-IS (x ∷ []) = x
Last*-IS [] = ⊥-IS

CombineSyn* : ∀{ISs} → ISTelescope ISs → SynImpl (BinCoproduct*-IS ISs) (Last*-IS ISs) 
CombineSyn* (Base-IST {IS}) = free-SynImpl lem
  where lem : ISMorphism (IS ⊎-IS ⊥-IS) IS
        lem = {!!}
CombineSyn* (Cons-IST I Is) = {!!} 

ComposeSyn* : ∀{ISs} → ISTelescope ISs → SynImpl (First*-IS ISs) (Last*-IS ISs)
ComposeSyn* Base-IST = {!!}
ComposeSyn* (Cons-IST I Is) = {!!}
  
