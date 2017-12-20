module Utility.Product where

open import ThesisPrelude
open import Algebra.Function

fst-Retraction : ∀{l} {A B : Set l} (b : B)
               → Retraction fst {A = A} of λ x → x , b
fst-Retraction b = λ a → refl
