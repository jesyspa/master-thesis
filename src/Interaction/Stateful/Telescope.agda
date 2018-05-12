module Interaction.Stateful.Telescope where

open import ThesisPrelude
open import Interaction.Stateful.InteractionStructure
open import Interaction.Stateful.Implementation

data Telescope : List InteractionStructure
               → List InteractionStructure
               → Set where
  Empty : Telescope [] []
  _▹_   : ∀{IS JS ISs JSs}
        → SynImpl IS (BinTensor*-IS (JS ∷ ISs))
        → Telescope ISs JSs
        → Telescope (IS ∷ ISs) (JS ∷ JSs)

module _ {IS JS ISs JSs} where
  combine : SynImpl IS (BinTensor*-IS (JS ∷ ISs))
          → Telescope ISs JSs
          → SynImpl (BinTensor*-IS (IS ∷ ISs)) (BinTensor*-IS (JS ∷ JSs))
  combine si Empty = binmap-SI (si ∘′-SI fmap-IS-SynImpl RightCancel-IS) id-SI
  combine si (sj ▹ ts) = binmap-SI {!!} {!!}
