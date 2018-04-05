open import Distribution.Class
open import Distribution.PropsClass
module Examples.Epsilon (M : Set → Set){{DM : DistMonad M}}{{DMP : DistMonadProps M}} where

open import ThesisPrelude
open import Probability.Class
open import Probability.PropsClass

open DistMonad DM
open DistMonadProps DMP
open ProbabilityProps is-probability

Q = probability

module _ {A}{{_ : Eq A}} where
  bounded-dist-diff-refl : (ε : Q)(D : M A) → (zro < ε) → bounded-dist-diff D D ε
  bounded-dist-diff-refl ε D pf a = bounded-diff-refl _ pf
  
  bounded-dist-diff-sym : (ε : Q){D₁ D₂ : M A}
                        → bounded-dist-diff D₁ D₂ ε
                        → bounded-dist-diff D₂ D₁ ε
  bounded-dist-diff-sym ε pf a = bounded-diff-sym (pf a)
  
  bounded-dist-diff-trans : (ε₁ ε₂ : Q){D₁ D₂ D₃ : M A}
                          → bounded-dist-diff D₁ D₂ ε₁
                          → bounded-dist-diff D₂ D₃ ε₂
                          → bounded-dist-diff D₁ D₃ (ε₁ + ε₂)
  bounded-dist-diff-trans ε₁ ε₂ bd₁ bd₂ a = bounded-diff-trans (bd₁ a) (bd₂ a)
