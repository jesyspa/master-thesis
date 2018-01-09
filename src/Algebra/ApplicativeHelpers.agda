module Algebra.ApplicativeHelpers where

open import ThesisPrelude

pairing-comb : ∀{l} {A B C D : Set l} (f : A → C → D) (g : B → C) → A × B → D
pairing-comb f g (a , b) = f a (g b)
