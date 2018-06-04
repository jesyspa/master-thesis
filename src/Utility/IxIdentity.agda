module Utility.IxIdentity {l l′} where

open import ThesisPrelude
open import Algebra.Indexed.Monad
open import Utility.Identity

-- The levels work out this way; I am not 100% sure why.
IxIdentity : {A : Set (lsuc l)} → (A → Set l′) → (A → Set l′)
IxIdentity {A} = Identity {l ⊔ l′} {A → Set l′}

open import Algebra.Indexed.LiftMonad

instance
  IxMonadIxIdentity : {A : Set (lsuc l)} → IxMonad {S = A} IxIdentity
  IxMonadIxIdentity {A} = IxMonadLiftM {l′} {S = A} Identity {{it}}
