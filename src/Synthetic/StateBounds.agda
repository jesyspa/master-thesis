{-# OPTIONS --type-in-type #-}
module Synthetic.StateBounds (ST : Set) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition

data NotAWrite : CryptoExprCmd → Set where
  Uniform-NAW : ∀{n} → NotAWrite (Uniform n)
  GetState-NAW : NotAWrite GetState

data NotARead : CryptoExprCmd → Set where
  Uniform-NAR : ∀{n} → NotARead (Uniform n)
  SetState-NAR : ∀{st} → NotARead (SetState st)

data NoWrites : ∀{A} → CryptoExpr A → Set₁ where
  Return-NW   : ∀{A}(a : A) → NoWrites (Return-FM a) 
  Uniform-NW  : ∀{A} n (cont : BitVec n → CryptoExpr A)
              → (∀ v → NoWrites (cont v))
              → NoWrites (Invoke-FM (Uniform n) cont)
  GetState-NW : ∀{A}(cont : ST → CryptoExpr A)
              → (∀ st → NoWrites (cont st))
              → NoWrites (Invoke-FM GetState cont)

data NoReads : ∀{A} → CryptoExpr A → Set₁ where
  Return-NR   : ∀{A}(a : A) → NoReads (Return-FM a) 
  Uniform-NR  : ∀{A} n (cont : BitVec n → CryptoExpr A)
              → (∀ v → NoReads (cont v))
              → NoReads (Invoke-FM (Uniform n) cont)
  SetState-NR : ∀{A} st (ce : CryptoExpr A)
              → (NoReads ce)
              → NoReads (Invoke-FM (SetState st) (const ce))
