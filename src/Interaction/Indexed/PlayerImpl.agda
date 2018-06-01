open import ThesisPrelude
open import Distribution.Class
module Interaction.Indexed.PlayerImpl (M : Set → Set){{_ : DistMonad M}} where

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
open import Algebra.Indexed.LiftMonad {lzero} M {{it}}
-- Aaaa no please why.
-- Okay, given a level l monad, how do we get a level lsuc l monad?
open import Utility.State.Indexed.ReindexingTransformer eval-SE LiftM

open IxMonad {{...}}

EvalCryptoState : Implementation CryptoExprIS IxStateTᵣ (id ***′ id)
EvalCryptoState = ?
