module Utility.List.Props where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Monoid
open import Utility.List.FunctorProps public
open import Utility.List.ApplicativeProps public
open import Utility.List.MonadProps public
open import Utility.List.MonoidProps public
open import Utility.List.ComplexProps public

∷-list-Inj : ∀{l} {A : Set l} (x : A)
           → Injective (List._∷_ {A = A} x)
∷-list-Inj x refl = refl

