open import Distribution.Class using (DistMonad)
module Distribution.ProperClass (F : Set → Set) {{DF : DistMonad F}} where

open DistMonad DF
open import ThesisPrelude
open import Algebra.FiniteSet

module _ {A}{{ULA : UniqueListable A}} where
  open UniqueListable ULA
  open Listable super-Enumeration
  record ProperDist (D : F A) : Set where
    field
      NonNegative : ∀ a → zro ≤ sample D a 
      SumOne : one ≡ sum (map (sample D) ListEnumeration)



