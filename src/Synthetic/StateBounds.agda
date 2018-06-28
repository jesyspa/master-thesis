{-# OPTIONS --type-in-type #-}
module Synthetic.StateBounds (ST : Set) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open FM
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition

open CommandStructure

data NotAWrite : CryptoExprCmd → Set where
  Uniform-NAW : ∀{n} → NotAWrite (Uniform n)
  GetState-NAW : NotAWrite GetState

data NotARead : CryptoExprCmd → Set where
  Uniform-NAR : ∀{n} → NotARead (Uniform n)
  SetState-NAR : ∀{st} → NotARead (SetState st)

data NoWrites : ∀{A} → CryptoExpr A → Set₁ where
  Return-NW   : ∀{A}(a : A) → NoWrites (Return-FM a) 
  Invoke-NW   : ∀{A} c {cont : Response CryptoExprCS c → CryptoExpr A}
              → NotAWrite c
              → (∀ r → NoWrites (cont r))
              → NoWrites (Invoke-FM c cont)

getNAWInvoke-NW : ∀{A c}{cont : Response CryptoExprCS c → CryptoExpr A}
               → NoWrites (Invoke-FM c cont) → NotAWrite c
getNAWInvoke-NW (Invoke-NW c naw ncont) = naw
getNWInvoke-NW : ∀{A c}{cont : Response CryptoExprCS c → CryptoExpr A}
              → NoWrites (Invoke-FM c cont) → ∀ r → NoWrites (cont r)
getNWInvoke-NW (Invoke-NW c naw ncont) = ncont

data NoReads : ∀{A} → CryptoExpr A → Set₁ where
  Return-NR   : ∀{A}(a : A) → NoReads (Return-FM a) 
  Invoke-NR   : ∀{A} c {cont : Response CryptoExprCS c → CryptoExpr A}
              → NotARead c
              → (∀ r → NoReads (cont r))
              → NoReads (Invoke-FM c cont)

getNARInvoke-NR : ∀{A c}{cont : Response CryptoExprCS c → CryptoExpr A}
               → NoReads (Invoke-FM c cont) → NotARead c
getNARInvoke-NR (Invoke-NR c naw ncont) = naw
getNRInvoke-NR : ∀{A c}{cont : Response CryptoExprCS c → CryptoExpr A}
              → NoReads (Invoke-FM c cont) → ∀ r → NoReads (cont r)
getNRInvoke-NR (Invoke-NR c naw ncont) = ncont
