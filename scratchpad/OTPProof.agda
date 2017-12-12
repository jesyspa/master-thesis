module OTPProof where

open import MyPrelude
open import UFValuation
open import UniformFreeMonad
open import AbstractDist
open import BitVec

expr-A : ∀ n (v : BitVec n) → UniformFree (BitVec n)
expr-A n v = uniformUF n λ x → returnUF (bv-xor v x)

expr-B : ∀ n → UniformFree (BitVec n)
expr-B n = uniformUF n returnUF

-- we want some extensional notion of equality here
goal : ∀ n v → ⟦ expr-A n v ⟧ ≡ ⟦ expr-B n ⟧
goal n v = {!!}
