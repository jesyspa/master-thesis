{-# OPTIONS --allow-unsolved-metas #-}
module Carrier.Class where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Preorder

-- A carrier is a Semiring that is also an Ord.
-- Can we express that somehow?

record Carrier (A : Set) : Set₁ where
  field
    overlap {{super-semiring}} : Semiring A
    overlap {{super-ord}} : Ord A
    pow2 : Nat → A
    negpow2 : Nat → A

open Carrier {{...}} public

{-# DISPLAY Carrier.pow2 _ n = pow2 n #-}
{-# DISPLAY Carrier.negpow2 _ n = negpow2 n #-}

record CarrierProps (A : Set) {{C : Carrier A}} : Set where
  field
    +-is-comm-monoid    : CommMonoidProps A {{+-monoid}}
    *-is-monoid         : MonoidProps A {{*-monoid}}
    +*-left-dist        : (a b c : A) → a * (b + c) ≡ a * b + a * c
    +*-right-dist       : (a b c : A) → (a + b) * c ≡ a * b + a * c
    zro-left-nil        : (a : A) → a ≡ zro * a
    zro-right-nil       : (a : A) → a ≡ a * zro
    ≤-is-preorder       : PreorderProps A
    zro-minimum         : (a : A) → zro ≤ a
    -- TODO: Figure out why we need the 'Carrier.' here
    pow2-add            : ∀ n → pow2 {{C}} (suc n) ≡ pow2 n + pow2 n
    negpow2-add         : ∀ n → negpow2 {{C}} n ≡ negpow2 (suc n) + pow2 (suc n)
    pow2-negpow2-cancel : ∀ n → one ≡ pow2 {{C}} n * negpow2 n
    pow2-zro-one        : one ≡ pow2 {{C}} zro
  *-unit-left : (a : A) → a ≡ one * a
  *-unit-left = MonoidProps.unit-left {{*-monoid}} *-is-monoid
  +-unit-left : (a : A) → a ≡ zro + a
  +-unit-left = MonoidProps.unit-left {{+-monoid}} (super +-is-comm-monoid)
  +-unit-right : (a : A) → a ≡ a + zro
  +-unit-right = MonoidProps.unit-right {{+-monoid}} (super +-is-comm-monoid)

  negpow2-zro-one : one ≡ negpow2 {{C}} zro
  negpow2-zro-one =
    one
      ≡⟨ pow2-negpow2-cancel zro ⟩
    pow2 zro * negpow2 zro
      ≡⟨ cong (λ e → e * negpow2 zro) pow2-zro-one ⟩ʳ
    one * negpow2 zro
      ≡⟨ *-unit-left (negpow2 zro) ⟩ʳ
    negpow2 zro
    ∎

open CarrierProps {{...}} public
