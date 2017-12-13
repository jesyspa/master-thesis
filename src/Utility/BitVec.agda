module Utility.BitVec where

open import ThesisPrelude

abstract
  BitVec : Nat → Set
  BitVec = Vec Bool

postulate
  instance
    EqBitVec : ∀{n} → Eq (BitVec n)

  bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
  all-bitvecs : ∀ n → List (BitVec n)
