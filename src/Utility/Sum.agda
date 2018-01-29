module Utility.Sum where

open import ThesisPrelude

codiag : ∀{l}{A : Set l} → Either A A → A
codiag (left a) = a
codiag (right a) = a
