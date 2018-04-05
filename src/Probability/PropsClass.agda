open import Probability.Class using (Probability)
module Probability.PropsClass (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Utility.Num
open import Algebra.Monoid
open import Algebra.Function
open import Algebra.Preorder Q
open import Algebra.SemiringProps Q
open import Algebra.SubtractiveProps Q
open import Probability.Class

record ProbabilityProps : Set where
  open Probability PQ
  field
    overlap {{srprops}}  : SemiringProps
    overlap {{subprops}} : SubtractiveProps
    overlap {{poprops}}  : PreorderProps
  open SemiringProps    srprops
  open SubtractiveProps subprops
  open PreorderProps    poprops
  field
    *-comm              : (a b : Q) → a * b ≡ b * a
    neg-is-+-inv        : (a : Q) → zro ≡ a + negate a
    embed-Inj           : Injective embed
    *-Inj               : (a : Q) → ¬ (a ≡ zro) → Injective (_*_ a)
    pow2-negpow2-cancel : ∀ n → one ≡ embed (pow2 n) * negpow2 n
    abs-zro             : (a : Q) → (zro ≤ a) → a ≡ abs a
    abs-nonneg          : (a : Q) → zro ≤ abs a
    abs-sub-sym         : (a b : Q) → abs (a - b) ≡ abs (b - a) 
    abs-plus-dist       : (a b : Q) → abs (a + b) ≤ abs a + abs b
    ≤-dist-+            : {a b c d : Q} → a ≤ c → b ≤ d → a + b ≤ c + d
    <-dist-+            : {a b c d : Q} → a < c → b < d → a + b < c + d

  embed-1 : one ≡ embed 1
  embed-1 = +-unit-left one

  embed+ : ∀ n m → embed (n +N m) ≡ embed n + embed m
  embed+ zero m = +-unit-left (embed m)
  embed+ (suc n) m rewrite embed+ n m = +-assoc (embed n) (embed m) one
                                    ʳ⟨≡⟩ cong (_+_ (embed n)) (+-comm (embed m) one)
                                     ⟨≡⟩ +-assoc (embed n) one (embed m)

  embed* : ∀ n m → embed (n *N m) ≡ embed n * embed m
  embed* zero m = zro-left-nil (embed m)
  embed* (suc n) m rewrite embed+ m (n *N m) |
                           embed* n m        = +-comm (embed m) (embed n * embed m)
                                            ⟨≡⟩ cong (_+_ (embed n * embed m)) (*-unit-left (embed m))
                                            ⟨≡⟩ʳ +*-right-dist (embed n) one (embed m)

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

  bounded-diff-refl : (a : Q){ε : Q} → (zro < ε) → bounded-diff a a ε
  bounded-diff-refl a pf rewrite sub-cancelling a | sym (abs-zro zro (≤-refl zro)) = pf

  bounded-diff-sym : {a b ε : Q} → bounded-diff a b ε → bounded-diff b a ε
  bounded-diff-sym {a} {b} bd rewrite abs-sub-sym a b = bd

  bounded-diff-trans : {a b c ε₁ ε₂ : Q}
                     → bounded-diff a b ε₁ → bounded-diff b c ε₂
                     → bounded-diff a c (ε₁ + ε₂)
  bounded-diff-trans {a} {b} {c} bd₁ bd₂ = <-transˡ lem2 (<-dist-+ bd₁ bd₂)
    where
      lem1 : a - c ≡ (a - b) + (b - c)
      lem1 = adj-plus (
        a
          ≡⟨ plus-sub-cancelling a b ⟩
        (a - b) + b
          ≡⟨ cong (λ e → (a - b) + e) (plus-sub-cancelling b c) ⟩
        (a - b) + ((b - c) + c)
          ≡⟨ +-assoc (a - b) (b - c) c ⟩
        (a - b) + (b - c) + c
        ∎)
      lem2 : abs (a - c) ≤ abs (a - b) + abs (b - c)
      lem2 rewrite lem1 = abs-plus-dist (a - b) (b - c)

  negpow2-add : ∀ n → negpow2 n ≡ negpow2 (suc n) + negpow2 (suc n)
  negpow2-add n = *-Inj (embed (pow2 n)) lem-embed-nz (
    embed (pow2 n) * negpow2 n 
      ≡⟨ pow2-negpow2-cancel n ⟩ʳ
    one
      ≡⟨ pow2-negpow2-cancel (suc n) ⟩
    embed (pow2 (suc n)) * negpow2 (suc n)
      ≡⟨ cong (λ e → embed e * negpow2 (suc n)) (pow2 (suc n) ≡⟨ auto ⟩ pow2 n *N 2 ∎) ⟩
    embed (pow2 n *N 2) * negpow2 (suc n)
      ≡⟨ cong (λ e → e * negpow2 (suc n)) (embed* (pow2 n) 2) ⟩
    embed (pow2 n) * embed 2 * negpow2 (suc n)
      ≡⟨ *-assoc (embed (pow2 n)) (embed 2) (negpow2 (suc n)) ⟩ʳ
    embed (pow2 n) * (embed 2 * negpow2 (suc n))
      ≡⟨ cong (_*_ (embed (pow2 n))) (lem+ (negpow2 (suc n))) ⟩
    embed (pow2 n) * (negpow2 (suc n) + negpow2 (suc n))
    ∎)
    where
      lem2 : embed 2 ≡ one + one
      lem2 rewrite sym embed-1 = refl
      lem+ : (a : Q) → embed 2 * a ≡ a + a
      lem+ a = cong (λ e → e * a) lem2
            ⟨≡⟩ +*-right-dist one one a
            ⟨≡⟩ cong₂ _+_ (sym (*-unit-left a)) (sym (*-unit-left a)) 
      lem-embed-nz : ¬ (embed (pow2 n) ≡ zro)
      lem-embed-nz p = pow2-nz n (embed-Inj p)
