open import ThesisPrelude
module Algebra.Indexed.Monad {l l′}{S : Set l}(M : (S → Set l′) → S → Set l′) where

record IxMonad : Set (lsuc l′ ⊔ l) where
  infixl 1 _>>=ⁱ_
  field
    returnⁱ : ∀{A s} → A s → M A s
    _>>=ⁱ_ : ∀{A B s} → M A s → (∀{s′} → A s′ → M B s′) → M B s


