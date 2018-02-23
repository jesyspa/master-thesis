module Utility.State.Definition {l} where

open import ThesisPrelude
open import Utility.Identity
open import Algebra.Parametrised.Monad
open import Utility.State.Transformer (λ _ _ → Identity) {{triviallyPar (Set l) Identity}}

ParState : Set l → Set l → Set l → Set l
ParState = ParStateT
