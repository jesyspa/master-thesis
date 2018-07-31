module Algebra.Indexed.Functor {S : Set}(F : (S → Set) → S → Set) where

open import ThesisPrelude

-- This is an experiment; in practice, we care little for things that are merely indexed functors.
-- As such, fmapⁱ stays in the IxMonad record and here we use ixfmap.
-- For similar reasons, we don't use universe levels. 
record IxFunctor : Set₁ where
  field
    ixfmap : ∀{A B s} → (∀{s′} → A s′ → B s′) → F A s → F B s

-- The notion of morphisms for indexed functors is the same as for indexed monads, just without
-- certain laws (which we haven't written out anyway).
