module Utility.State.Definition {l} where

open import ThesisPrelude
open import Utility.Identity {l}
open import Algebra.Parametrised.Monad
open import Algebra.Parametrised.Lift (Set l) Identity
open import Utility.State.Transformer Lifted

ParState : Set l → Set l → Set l → Set l
ParState = ParStateT
