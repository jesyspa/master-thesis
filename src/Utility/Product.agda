module Utility.Product where

open import ThesisPrelude
open import Algebra.Function

fst-Retraction : ∀{l} {A B : Set l} (b : B)
               → Retraction fst {A = A} of λ x → x , b
fst-Retraction b = λ a → refl

rev-pair : ∀{l}{A B : Set l} → B → A → A × B
rev-pair = flip _,_
  
over-fst : ∀{l} {A B C : Set l} (f : A → C) → A × B → C × B
over-fst f (a , b) = f a , b

over-snd : ∀{l} {A B C : Set l} (f : B → C) → A × B → A × C
over-snd f (a , b) = a , f b

diag : ∀{l} {A : Set l} → A → A × A
diag a = a , a
