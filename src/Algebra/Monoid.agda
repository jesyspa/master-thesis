module Algebra.Monoid where

open import ThesisPrelude

record MonoidProps (A : Set) {{M : Monoid A}} : Set where
  field
    op-assoc   : (a b c : A) → a <> (b <> c) ≡ (a <> b) <> c
    unit-left  : (a : A)     → a ≡ mempty <> a
    unit-right : (a : A)     → a ≡ a <> mempty

open MonoidProps {{...}} public

record CommMonoidProps (A : Set) {{M : Monoid A}} : Set where
  field
    op-comm : (a b : A) → a <> b ≡ b <> a
    overlap {{super}} : MonoidProps A

open CommMonoidProps {{...}} public

+-monoid : {A : Set} {{_ : Semiring A}} → Monoid A
+-monoid = record { mempty = zro ; _<>_ = _+_ }

*-monoid : {A : Set} {{_ : Semiring A}} → Monoid A
*-monoid = record { mempty = one ; _<>_ = _*_ }
