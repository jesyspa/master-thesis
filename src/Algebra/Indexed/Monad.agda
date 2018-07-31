open import ThesisPrelude
module Algebra.Indexed.Monad {l l′}{S : Set l}(M : (S → Set l′) → S → Set l′) where

record IxMonad : Set (lsuc l′ ⊔ l) where
  infixl 1 _>>=ⁱ_
  field
    fmapⁱ : ∀{A A′ s} → (∀{s′} → A s′ → A′ s′) → M A s → M A′ s
    returnⁱ : ∀{A s} → A s → M A s
    _>>=ⁱ_ : ∀{A B s} → M A s → (∀{s′} → A s′ → M B s′) → M B s

  joinⁱ : ∀{A s} → M (M A) s → M A s
  joinⁱ m = m >>=ⁱ id
