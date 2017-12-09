module Semigroup where

open import MiniPrelude

record Semigroup (A : Set) : Set where
  infix 8 _^_
  field 
    _^_ : A → A → A
    semigroup-assoc : ∀ i j k → i ^ (j ^ k) ≡ (i ^ j) ^ k

open Semigroup {{...}} public

