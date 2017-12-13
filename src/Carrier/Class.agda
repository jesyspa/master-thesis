module Carrier.Class where

open import ThesisPrelude
open import Algebra.Monoid
open import Algebra.Preorder

-- A carrier is a Semiring that is also an Ord.
-- Can we express that somehow?

record Carrier (A : Set) : Set where
  field
    pow2 : Nat → A
    negpow2 : Nat → A
    overlap {{super}} : Semiring A

open Carrier {{...}} public

record CarrierProps (A : Set) {{_ : Ord A}} {{C : Carrier A}} : Set where
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
    pow2-add            : ∀ n → Carrier.pow2 C (suc n) ≡ pow2 n + pow2 n
    negpow2-add         : ∀ n → Carrier.negpow2 C n ≡ negpow2 (suc n) + pow2 (suc n)
    pow2-negpow2-cancel : ∀ n → one ≡ Carrier.pow2 C n * negpow2 n
    pow2-zro-one        : one ≡ Carrier.pow2 C zro

open CarrierProps {{...}} public
