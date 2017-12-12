module AbstractHelpers where

open import MyPrelude
open import AbstractProb
open import Monoid

sumXF : List XFixed → XFixed
sumXF = mconcat {{AddMonoid-XF}}

