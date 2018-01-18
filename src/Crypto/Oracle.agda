{-# OPTIONS --allow-unsolved-metas #-}
module Crypto.Oracle where

open import ThesisPrelude
open import Crypto.Syntax

-- We want a "opaque" way of passing S around.
-- The CPAAdv can NOT inspect it!

-- AG: monad state in CPS style?
CE : (S A : Set) → Set
CE = {!!}

record Oracle (In Out S : Set) : Set₁ where
  constructor oracle
  field
    query : In → CE S Out
