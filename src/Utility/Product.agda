module Utility.Product where

open import ThesisPrelude
open import Algebra.Function

fst-Retraction : ∀{l} {A B : Set l} (b : B)
               → Retraction fst {A = A} of λ x → x , b
fst-Retraction b = λ a → refl

rev-pair : ∀{l}{A B : Set l} → B → A → A × B
rev-pair = flip _,_

diag : ∀{l} {A : Set l} → A → A × A
diag a = a , a
