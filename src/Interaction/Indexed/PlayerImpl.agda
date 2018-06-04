open import ThesisPrelude
open import Distribution.Class
module Interaction.Indexed.PlayerImpl (M : Set → Set){{DMM : DistMonad M}} where

open import Algebra.Function
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.Implementation
open import Interaction.Indexed.Telescope
open import Interaction.Indexed.CryptoExpr
open import Interaction.Indexed.StateExpr
open import Interaction.Indexed.Joinable
open import Interaction.Indexed.Player
open import Algebra.Indexed.LiftMonad {lzero} {S = ⊤} M {{it}}
open import Utility.State.Indexed.FromUniverseTransformer eval-SE LiftM {{it}}

open InteractionStructure
open IxMonad {{...}}
open DistMonad DMM
open Implementation

EvalCryptoState : Implementation CryptoStateIS IxStateT id 
RunImpl EvalCryptoState {s , tt} (left (modify-SE s′ f))
  = fmapⁱ {s = s , tt} (λ { (V r) → StrongV r refl }) (modifyT f)
RunImpl EvalCryptoState {s , tt} (right (uniform-CE n))
  = map-liftT s (λ v → StrongV v refl) (uniform n)
