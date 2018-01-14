open import Probability.Class using (Probability)
module Probability.PropsClass (A : Set) {{PA : Probability A}} where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Preorder
open import Algebra.SemiringProps A
open SemiringProps {{...}}
open import Probability.Class

record ProbabilityProps : Set where
  field
    overlap {{srprops}} : SemiringProps
    ≤-is-preorder       : PreorderProps A
    pow2-add            : ∀ n → pow2 (suc n) ≡ pow2 n + pow2 n as A
    negpow2-add         : ∀ n → negpow2 n ≡ negpow2 (suc n) + pow2 (suc n) as A
    pow2-negpow2-cancel : ∀ n → one ≡ pow2 n * negpow2 n
    pow2-zro-one        : one ≡ pow2 zro

  negpow2-zro-one : one ≡ negpow2 zro
  negpow2-zro-one =
    one
      ≡⟨ pow2-negpow2-cancel zro ⟩
    pow2 zro * negpow2 zro
      ≡⟨ cong (λ e → e * negpow2 zro) pow2-zro-one ⟩ʳ
    one * negpow2 zro
      ≡⟨ *-unit-left (negpow2 zro) ⟩ʳ
    negpow2 zro
    ∎
