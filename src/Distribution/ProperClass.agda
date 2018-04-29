open import Distribution.Class using (DistMonad)
module Distribution.ProperClass (F : Set → Set) {{DF : DistMonad F}} where

open DistMonad DF
open import ThesisPrelude
open import Algebra.FiniteSet

module _ {A}{{_ : FiniteSet A}} where
  record ProperDist (D : F A) : Set where
    field
      non-negative : ∀ a → zro ≤ sample D a 
      sum-one : one ≡ sum (map (sample D) (finite-set-list A))



