open import ThesisPrelude
module Algebra.Indexed.LiftMonad {l l′}{S : Set l′}(M : Set l → Set l){{_ : Monad M}} where

LiftM : (S → Set l) → S → Set l
LiftM A s = M (A s)

open import Algebra.Indexed.Monad LiftM
open IxMonad

instance
  IxMonadLiftM : IxMonad
  returnⁱ IxMonadLiftM a = return a
  _>>=ⁱ_  IxMonadLiftM m f = m >>= f
  fmapⁱ   IxMonadLiftM f m = fmap f m
