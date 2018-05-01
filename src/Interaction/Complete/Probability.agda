open import Distribution.Class
module Interaction.Complete.Probability (D : Set → Set){{DMD : DistMonad D}} where

open import ThesisPrelude
open import Algebra.FiniteSet
open import Distribution.PropsClass
open import Interaction.Complete.CryptoExpr
open import Interaction.Complete.FreeMonad
open import Interaction.Complete.Implementation

open DistMonad DMD

crypto-impl : Implementation CryptoExprIS D
crypto-impl (uniform-CE n) = uniform n

⟦_⟧ : ∀{A} → FreeMonad CryptoExprIS A → D A
⟦_⟧ = lift-Impl crypto-impl

syn-equiv : ∀{A}{{_ : Eq A}}
          → (e₁ e₂ : FreeMonad CryptoExprIS A)
          → Set
syn-equiv e₁ e₂ = ⟦ e₁ ⟧ ≡D ⟦ e₂ ⟧

syn-bounded-diff : ∀{A}{{_ : FiniteSet A}}
                 → (e₁ e₂ : FreeMonad CryptoExprIS A)
                 → probability
                 → Set
syn-bounded-diff e₁ e₂ ε = bounded-dist-diff ⟦ e₁ ⟧ ⟦ e₂ ⟧ ε

