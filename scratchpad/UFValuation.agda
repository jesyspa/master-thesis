module UFValuation where

open import MyPrelude
open import UniformFreeMonad
open import AbstractDist

⟦_⟧ : ∀{A} → UniformFree A → ADist A
⟦ returnUF x ⟧ = returnA x
⟦ uniformUF n f ⟧ = uniformA n >>=A λ v → ⟦ f v ⟧
