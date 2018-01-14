module Probability.Class where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Preorder

-- A probability is a Semiring that is also an Ord and supports negative powers of two.

record Probability (A : Set) : Set₁ where
  field
    overlap {{super-semiring}} : Semiring A
    overlap {{super-ord}} : Ord A
    pow2 : Nat → A
    negpow2 : Nat → A

open Probability {{...}} public

{-# DISPLAY Probability.pow2 _ n = pow2 n #-}
{-# DISPLAY Probability.negpow2 _ n = negpow2 n #-}

