module Synthetic.Enumeration where

open import ThesisPrelude
open import Utility.List.Elem.Definition

record Enumeration (A : Set) : Set where
  field
    Enumerate : List A
    EnumerateComplete : ∀ a → a ∈ Enumerate
    EnumerateUnique : ∀{a}(p q : a ∈ Enumerate) → p ≡ q
