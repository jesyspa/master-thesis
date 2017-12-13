module Algebra.Preorder where

open import ThesisPrelude

record PreorderProps (A : Set) {{_ : Ord A}} : Set where
  field
    ≤-refl  : (a : A)                     → a ≤ a
    ≤-trans : (a b c : A) → a ≤ b → b ≤ c → a ≤ c

open PreorderProps {{...}} public
