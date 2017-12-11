module AbstractHelpers where

open import MyPrelude
open import AbstractProb

sumF : ∀{n} → List (Fixed n) → XFixed
sumF [] = 0XF
sumF (x ∷ xs) = toXFixed x +XF sumF xs

