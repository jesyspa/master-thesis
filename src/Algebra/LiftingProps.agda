import ThesisPrelude as TP 
module Algebra.LiftingProps {l l′} (F : Set l → Set l′) {{FF : TP.Functor F}} where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.FunctorProps F

module _ {{FPF : FunctorProps}} where
  open FunctorProps FPF
  module _ {A B : Set l} where
    fmap-lift-Bij : (f : A → B) → Bijective f → Bijective (fmap-F f)
    fmap-lift-Bij f (fi , ps , pr) = fmap fi , fmap-lift-ret fi f ps , fmap-lift-ret f fi pr
