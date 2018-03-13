open import Probability.Class using (Probability)
module Probability.PropsClass (A : Set) {{PA : Probability A}} where

open import ThesisPrelude
open import Utility.Num
open import Algebra.Monoid
open import Algebra.Preorder
open import Algebra.Function
open import Algebra.SemiringProps A
open import Probability.Class

record ProbabilityProps : Set where
  open Probability PA
  field
    overlap {{srprops}} : SemiringProps
    overlap {{poprops}} : PreorderProps A
  open SemiringProps srprops
  field
    embed-Inj           : Injective embed
    *-comm              : (a b : A) → a * b ≡ b * a
    embed-zero          : zro ≡ embed 0
    embed-succ          : ∀ n → one + embed n ≡ embed (suc n)
    negpow2-add         : ∀ n → negpow2 n ≡ negpow2 (suc n) + negpow2 (suc n)
    pow2-negpow2-cancel : ∀ n → one ≡ embed (pow2 n) * negpow2 n

  embed-one : one ≡ embed 1
  embed-one = +-unit-right one ⟨≡⟩ cong (λ e → one + e) embed-zero ⟨≡⟩ embed-succ zero

  non-trivial : ¬(zro ≡ one as A)
  non-trivial p with embed-Inj (embed-zero ʳ⟨≡⟩ p ⟨≡⟩ embed-one)
  ... | ()

  negpow2-zro-one : one ≡ negpow2 zro
  negpow2-zro-one =
    one
      ≡⟨ pow2-negpow2-cancel zro ⟩
    embed (pow2 0) * negpow2 zro
      ≡⟨ cong (λ e → e * negpow2 zro) embed-one ⟩ʳ
    one * negpow2 zro
      ≡⟨ *-unit-left (negpow2 zro) ⟩ʳ
    negpow2 zro
    ∎
