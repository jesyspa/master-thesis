open import ThesisPrelude using (Semiring)
module Algebra.SemiringProps (A : Set) {{SA : Semiring A}} where

open import ThesisPrelude
open import Algebra.Monoid

record SemiringProps : Set where
  field
    +-is-comm-monoid    : CommMonoidProps A {{+-monoid}}
    *-is-monoid         : MonoidProps A {{*-monoid}}
    +*-left-dist        : (a b c : A) → a * (b + c) ≡ a * b + a * c
    +*-right-dist       : (a b c : A) → (a + b) * c ≡ a * b + a * c
    zro-left-nil        : (a : A) → a ≡ zro * a
    zro-right-nil       : (a : A) → a ≡ a * zro
  *-unit-left : (a : A) → a ≡ one * a
  *-unit-left = MonoidProps.unit-left {{*-monoid}} *-is-monoid
  +-unit-left : (a : A) → a ≡ zro + a
  +-unit-left = MonoidProps.unit-left {{+-monoid}} (super +-is-comm-monoid)
  +-unit-right : (a : A) → a ≡ a + zro
  +-unit-right = MonoidProps.unit-right {{+-monoid}} (super +-is-comm-monoid)
