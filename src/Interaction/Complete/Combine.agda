module Interaction.Complete.Combine where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.SyntacticImplementation 

module _ {def₁ def₂ : SyntaxDef} where
  CombineSyn : SyntacticImplementation (BinExtend-SD def₁ def₂)
             → SyntacticImplementation def₂
             → SyntacticImplementation (BinJoin-SD def₁ def₂)
  CombineSyn I₁ I₂ = BinMatch-SynI (comp-SynI I₁ (BinMatch-SynI (free-SynImpl (InclL-IS _ _))
                                                                (comp-SynI I₂ (free-SynImpl (InclR-IS _ _)))))
                                   (comp-SynI I₂ (free-SynImpl (InclR-IS _ _)))

data DepSynImplList : List SyntaxDef → Set₁ where
  Nil-DSIL  : DepSynImplList []
  Cons-DSIL : ∀{def defs}
            → SyntacticImplementation (BinExtend*-SD def defs)
            → DepSynImplList defs
            → DepSynImplList (def ∷ defs)


