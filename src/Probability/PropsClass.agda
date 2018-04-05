open import Probability.Class using (Probability)
module Probability.PropsClass (A : Set) {{PA : Probability A}} where

open import ThesisPrelude
open import Utility.Num
open import Algebra.Monoid
open import Algebra.Preorder A
open import Algebra.SemiringProps A
open import Algebra.SubtractiveProps A
open import Probability.Class

record ProbabilityProps : Set where
  open Probability PA
  field
    overlap {{srprops}}  : SemiringProps
    overlap {{subprops}} : SubtractiveProps
    overlap {{poprops}}  : PreorderProps
  open SemiringProps    srprops
  open SubtractiveProps subprops
  open PreorderProps    poprops
  field
    *-comm              : (a b : A) → a * b ≡ b * a
    embed-zero          : zro ≡ embed 0
    embed-succ          : ∀ n → one + embed n ≡ embed (suc n)
    negpow2-add         : ∀ n → negpow2 n ≡ negpow2 (suc n) + negpow2 (suc n)
    pow2-negpow2-cancel : ∀ n → one ≡ embed (pow2 n) * negpow2 n
    abs-zro             : (a : A) → (zro ≤ a) → a ≡ abs a
    abs-nonneg          : (a : A) → zro ≤ abs a
    abs-sub-sym         : (a b : A) → abs (a - b) ≡ abs (b - a) 
    abs-plus-dist       : (a b : A) → abs (a + b) ≤ abs a + abs b

  embed-1 : one ≡ embed 1
  embed-1 = +-unit-right one ⟨≡⟩ cong (λ e → one + e) embed-zero ⟨≡⟩ embed-succ zero

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

  bounded-diff-refl : (a ε : A) → (zro < ε) → bounded-diff a a ε
  bounded-diff-refl a ε pf rewrite sub-cancelling a | sym (abs-zro zro (≤-refl zro)) = pf

  bounded-diff-sym : (a b ε : A) → bounded-diff a b ε → bounded-diff b a ε
  bounded-diff-sym a b ε bd rewrite abs-sub-sym a b = bd

  bounded-diff-trans : (a b c ε₁ ε₂ : A)
                     → bounded-diff a b ε₁ → bounded-diff b c ε₂
                     → bounded-diff a c (ε₁ + ε₂)
  bounded-diff-trans a b c ε₁ ε₂ bd₁ bd₂ = {!!}
    where
      lem1 : a - c ≡ (a - b) + (b - c)
      lem1 = adj-plus (
        a
          ≡⟨ {!!} ⟩
        (a - b) + b
          ≡⟨ cong (λ e → (a - b) + e) (plus-sub-cancelling b c) ⟩
        (a - b) + ((b - c) + c)
          ≡⟨ {!+-assoc ? ? ?!} ⟩
        (a - b) + (b - c) + c
        ∎)
