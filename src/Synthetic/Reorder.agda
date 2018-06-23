{-# OPTIONS --type-in-type #-}
open import Synthetic.Enumeration
module Synthetic.Reorder (ST : Set){{EST : Enumeration ST}} where

open import ThesisPrelude
open import Synthetic.CommandStructure
open import Synthetic.EnumerationInstances
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions

open CommandStructure
open Enumeration {{...}}
     
maximum : List Nat → Nat
maximum = foldr max zero

maximumOf : ∀{A}{{_ : Enumeration A}}
          → (f : A → Nat)
          → Nat
maximumOf f = maximum (map f Enumerate)

instance
  EnumerationResponses : ∀ c → Enumeration (Response CryptoExprCS c)
  EnumerationResponses (Uniform n) = EnumerationBitVec n
  EnumerationResponses  GetState = EST
  EnumerationResponses (SetState _) = it

compute-max-CA : CommandAlgebra Nat
compute-max-CA c cont = maximumOf cont

get-randomness-Cmd : CryptoExprCmd → Nat
get-randomness-Cmd (Uniform n)  = n
get-randomness-Cmd  GetState    = zero
get-randomness-Cmd (SetState _) = zero

get-randomness-CA : CommandAlgebra Nat
get-randomness-CA = augment-algebra get-randomness-Cmd _+_ compute-max-CA

get-randomness : ∀{A} → CryptoExpr A → Nat
get-randomness = fold-algebra get-randomness-CA (const zero)

get-final-state-fun : ∀{A} → (ce : CryptoExpr A) → ST → BitVec (get-randomness ce) → ST
get-final-state-fun (Return-FM _) st v = st
get-final-state-fun (Invoke-FM (Uniform n) cont) st v with get-randomness (Invoke-FM (Uniform n) cont)
get-final-state-fun (Invoke-FM (Uniform n) cont) st v | y = {!!}
get-final-state-fun (Invoke-FM  GetState cont) st v = {!!}
get-final-state-fun (Invoke-FM (SetState st) cont) _ v = {!!}
