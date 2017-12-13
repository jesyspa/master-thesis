module Utility.BitVec where

open import ThesisPrelude
open import Utility.VecFuns
open import Utility.VecProps

BitVec : Nat → Set
BitVec = Vec Bool

postulate
  bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
  all-bitvecs : ∀ n → List (BitVec n)
