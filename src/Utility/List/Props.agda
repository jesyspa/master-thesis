module Utility.List.Props where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Monoid
open import Utility.List.Props.Functor public
open import Utility.List.Props.Applicative public
open import Utility.List.Props.Monad public
open import Utility.List.Props.Monoid public
open import Utility.List.Props.Complex public

∷-list-Inj : ∀{l} {A : Set l} (x : A)
           → Injective (List._∷_ {A = A} x)
∷-list-Inj x refl = refl

