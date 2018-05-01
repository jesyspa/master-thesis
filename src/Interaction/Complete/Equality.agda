open import Distribution.Class
module Interaction.Complete.Equality (D : Set → Set){{DMD : DistMonad D}} where

open import ThesisPrelude
open import Algebra.FiniteSet
open import Distribution.PropsClass
open import Interaction.Complete.CryptoExpr
open import Interaction.Complete.FreeMonad
open import Interaction.Complete.Implementation

open DistMonad DMD

crypto-impl : Implementation CryptoExprIS D
crypto-impl (uniform-CE n) = uniform n
