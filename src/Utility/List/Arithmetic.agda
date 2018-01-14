open import ThesisPrelude using (Semiring)
module Utility.List.Arithmetic (A : Set) {{SA : Semiring A}} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.SemiringProps A
open SemiringProps {{...}}

module _ {{_ : SemiringProps}} where
  singleton-sum-id : Retraction sum {A = A} of [_]
  singleton-sum-id x =
    x
      ≡⟨ +-unit-left x ⟩
    zro + x
      ≡⟨ forceLemma (zro + x) id ⟩ʳ
    force (zro + x) id
    ∎

{-
  sum-perm-invariant : PermInvariant {A = A} sum
  sum-perm-invariant [] φ = {!!}
  sum-perm-invariant (x ∷ xs) φ = {!!}
-}
