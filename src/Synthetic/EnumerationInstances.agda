{-# OPTIONS --type-in-type #-}
module Synthetic.EnumerationInstances where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Utility.Vector.Definition
open import Utility.Vector.BitVec
open import Utility.List.Elem.Definition

open Enumeration

instance
  Enumeration⊤ : Enumeration ⊤
  Enumerate         Enumeration⊤ = tt ∷ []
  EnumerateComplete Enumeration⊤ tt = here _ _
  EnumerateUnique   Enumeration⊤ p q = lem p ⟨≡⟩ʳ lem q 
    where lem : ∀{a}(p : a ∈ Enumerate Enumeration⊤) → p ≡ here _ _
          lem (here _ _) = refl
          lem (there _ _ _ ())

  EnumerationBitVec : ∀ n → Enumeration (BitVec n)
  Enumerate         (EnumerationBitVec n) = all-bitvecs n
  EnumerateComplete (EnumerationBitVec n) = all-bitvecs-complete
  EnumerateUnique   (EnumerationBitVec n) p q = all-bitvecs-unique _ p ⟨≡⟩ʳ all-bitvecs-unique _ q
