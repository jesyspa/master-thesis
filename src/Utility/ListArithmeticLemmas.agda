module Utility.ListArithmeticLemmas where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Permutation
open import Carrier.Class

module _ {A : Set} {{_ : Carrier A}} {{_ : CarrierProps A}} where
  singleton-sum-id : Retraction_of_ {A = A} sum [_]
  singleton-sum-id x =
    x
      ≡⟨ +-unit-left x ⟩
    zro + x
      ≡⟨ forceLemma (zro + x) id ⟩ʳ
    force (zro + x) id
    ∎

  sum-perm-invariant : PermInvariant {A = A} sum
  sum-perm-invariant [] φ = {!!}
  sum-perm-invariant (x ∷ xs) φ = {!!}
