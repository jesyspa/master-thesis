module Utility.State.Parametrised.Definition {l} where

open import ThesisPrelude
open import Utility.Identity {l}
open import Algebra.Parametrised.Monad
open import Algebra.Parametrised.Lift (⊤) Identity
open import Utility.State.Parametrised.Transformer Lifted

ParState : Set l → Set l → Set l → Set l
ParState S S′ = ParStateT (tt , S) (tt , S′)
