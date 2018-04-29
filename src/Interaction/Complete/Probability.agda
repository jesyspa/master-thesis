open import Distribution.Class
module Interaction.Complete.Probability (D : Set → Set){{DMD : DistMonad D}} where

open import ThesisPrelude
open import Interaction.Complete.CryptoExpr
open import Interaction.Complete.Implementation

open DistMonad DMD

⟦_⟧ : Implementation CryptoExprIS D
⟦ uniform-CE n ⟧ = uniform n

syn-bounded-diff : ∀{A}{{_ : Eq A}} → 
