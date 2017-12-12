module BitVec where

open import MyPrelude

abstract
  BitVec : Nat → Set
  BitVec = Vec Bool

postulate
  bv-xor : ∀{n} → BitVec n → BitVec n → BitVec n
