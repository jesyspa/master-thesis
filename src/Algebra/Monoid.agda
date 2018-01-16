import ThesisPrelude as TP
module Algebra.Monoid {l} (A : Set l) {{M : TP.Monoid A}} where

open import ThesisPrelude

record MonoidProps : Set l where
  field
    op-assoc   : (a b c : A) → a <> (b <> c) ≡ (a <> b) <> c
    unit-left  : (a : A)     → a ≡ mempty <> a
    unit-right : (a : A)     → a ≡ a <> mempty

record CommMonoidProps : Set l where
  field
    overlap {{forget-comm}} : MonoidProps
    op-comm : (a b : A) → a <> b ≡ b <> a

