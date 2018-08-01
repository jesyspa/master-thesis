module Utility.Vector.Definition where

open import ThesisPrelude
open import Utility.Vector.Functions
open import Utility.Bool

BitVec : Nat → Set
BitVec = Vec Bool

bitvec-xor : ∀{n} → BitVec n → BitVec n → BitVec n
bitvec-xor = vzip xor
