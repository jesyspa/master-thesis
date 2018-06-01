open import ThesisPrelude
module _ {𝑺 : Set}(M : Set → Set)(s : 𝑺){{DMM : DistMonad M}} where
module Interaction.Indexed.PlayerImpl {S\ where

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

open IxMonad {{...}}
