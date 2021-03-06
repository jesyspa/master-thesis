module Probability.Class where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Preorder

-- A probability type is a totally ordered ring of characteristic zero that has negative powers of two.

record Probability (Q : Set) : Set₁ where
  field
    overlap {{super-semiring}} : Semiring Q
    overlap {{super-subtractive}} : Subtractive Q
    overlap {{super-ord}} : Ord Q
    negpow2 : Nat → Q
    abs : Q → Q

  bounded-diff : Q → Q → Q → Set
  bounded-diff a b ε = abs (a - b) ≤ ε

  embed : Nat → Q
  embed zero = zro
  embed (suc n) = embed n + one

