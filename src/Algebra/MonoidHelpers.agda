module Algebra.MonoidHelpers {l} (A : Set l) where

open import ThesisPrelude

+-monoid : {{_ : Semiring A}} → Monoid A
+-monoid = record { mempty = zro ; _<>_ = _+_ }

*-monoid : {{_ : Semiring A}} → Monoid A
*-monoid = record { mempty = one ; _<>_ = _*_ }
