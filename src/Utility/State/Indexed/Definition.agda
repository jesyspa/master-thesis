module Utility.State.Indexed.Definition {l} where

open import ThesisPrelude
open import Utility.Identity {l}
open import Algebra.Indexed.Monad
open import Algebra.Indexed.LiftMonad Identity

open import Utility.State.Indexed.Transformer LiftM

IxState : (Set l → Set l) → (Set l → Set l)
IxState = IxStateT
