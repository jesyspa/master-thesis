open import Algebra.Indexed.Functor
module Algebra.Indexed.Free {S : Set}(F : (S → Set) → S → Set){{IxFF : IxFunctor F}} where

open import ThesisPrelude 

-- This non-positivity is quite a bit of a problem.
-- I guess this means that the indexed free monad doesn't exist?  That may be interesting to mention.
data IxFree : (S → Set) → S → Set where
  Return-IxFree : ∀{A s} → A s → IxFree A s
  Free-IxFree : ∀{A s} → F (IxFree A) s → IxFree A s
