module Algebra.Unit where

open import ThesisPrelude

⊤-final : ∀{l}{A : Set l} → A → ⊤
⊤-final _ = tt
