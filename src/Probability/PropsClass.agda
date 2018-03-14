open import Probability.Class using (Probability)
module Probability.PropsClass (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Utility.Num
open import Algebra.Monoid
open import Algebra.Function
open import Algebra.Preorder
open import Algebra.SemiringProps Q
open import Probability.Class

record ProbabilityProps : Set where
  open Probability PQ
  field
    overlap {{srprops}} : SemiringProps
    overlap {{poprops}} : PreorderProps Q
  open SemiringProps srprops
  field
    *-comm              : (a b : Q) → a * b ≡ b * a
    *-Inj               : (a : Q) → ¬ (a ≡ zro) → Injective (_*_ a)
    pow2-negpow2-cancel : ∀ n → one ≡ embed (pow2 n) * negpow2 n

  embed-1 : one ≡ embed 1
  embed-1 = +-unit-left one

  negpow2-zro-one : one ≡ negpow2 zro
  negpow2-zro-one =
    one
      ≡⟨ pow2-negpow2-cancel zro ⟩
    embed (pow2 0) * negpow2 zro
      ≡⟨ cong (λ e → e * negpow2 zro) embed-1 ⟩ʳ
    one * negpow2 zro
      ≡⟨ *-unit-left (negpow2 zro) ⟩ʳ
    negpow2 zro
    ∎

  negpow2-add : ∀ n → negpow2 n ≡ negpow2 (suc n) + negpow2 (suc n)
  negpow2-add n = *-Inj (embed (pow2 n)) {!!} (
    embed (pow2 n) * negpow2 n 
      ≡⟨ pow2-negpow2-cancel n ⟩ʳ
    one
      ≡⟨ {!!} ⟩
    embed (pow2 n) * embed 2 * negpow2 (suc n)
      ≡⟨ {!!} ⟩
    embed (pow2 n) * (negpow2 (suc n) + negpow2 (suc n))
    ∎)
