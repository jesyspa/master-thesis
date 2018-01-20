open import ThesisPrelude using (Semiring)
module Algebra.SemiringProps (A : Set) {{SA : Semiring A}} where

open import ThesisPrelude
open import Algebra.MonoidHelpers A
open import Algebra.Monoid A {{+-monoid}} using () renaming (MonoidProps to +MProps; CommMonoidProps to +CMProps)
open import Algebra.Monoid A {{*-monoid}} using () renaming (MonoidProps to *MProps) 

record SemiringProps : Set where
  field
    +-is-comm-monoid    : +CMProps
    *-is-monoid         : *MProps
    +*-left-dist        : (a b c : A) → a * (b + c) ≡ a * b + a * c
    +*-right-dist       : (a b c : A) → (a + b) * c ≡ a * c + b * c
    zro-left-nil        : (a : A) → zro ≡ zro * a
    zro-right-nil       : (a : A) → zro ≡ a * zro
  *-unit-left : (a : A) → a ≡ one * a
  *-unit-left = *MProps.unit-left *-is-monoid
  *-unit-right : (a : A) → a ≡ a * one
  *-unit-right = *MProps.unit-right *-is-monoid
  *-assoc : (a b c : A) → a * (b * c) ≡ (a * b) * c
  *-assoc = *MProps.op-assoc *-is-monoid
  +-unit-left : (a : A) → a ≡ zro + a
  +-unit-left = +MProps.unit-left (+CMProps.forget-comm +-is-comm-monoid)
  +-unit-right : (a : A) → a ≡ a + zro
  +-unit-right = +MProps.unit-right (+CMProps.forget-comm +-is-comm-monoid)
