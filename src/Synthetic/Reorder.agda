{-# OPTIONS --type-in-type #-}
open import Synthetic.Enumeration
module Synthetic.Reorder (ST : Set){{EST : Enumeration ST}} where

open import ThesisPrelude
open import Synthetic.CommandStructure
open import Synthetic.EnumerationInstances
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions
open import Utility.List.Elem.Definition
open import Utility.List.Elem.Map

open CommandStructure
open Enumeration {{...}}
     
maximum : List Nat → Nat
maximum = foldr max zero

postulate
  maximum-Max : ∀{n xs} → n ∈ xs → n ≤ maximum xs

maximumOf : ∀{A}{{_ : Enumeration A}}
          → (f : A → Nat)
          → Nat
maximumOf f = maximum (map f Enumerate)

maximumOf-Max : ∀{A}{{_ : Enumeration A}}
              → (f : A → Nat)
              → ∀ a → f a ≤ maximumOf f
maximumOf-Max f a = maximum-Max (map-preserves-in f _ _ (EnumerateComplete a)) 

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

get-randomness′ : ∀{A} → ST → CryptoExpr A → Nat
get-randomness′ st (Return-FM _) = zero
get-randomness′ st (Invoke-FM (Uniform n) cont) = n + maximumOf (λ v → get-randomness′ st (cont v))
get-randomness′ st (Invoke-FM  GetState cont) = get-randomness′ st (cont st)
get-randomness′ _  (Invoke-FM (SetState st) cont) = get-randomness′ st (cont tt)

data EnoughRandomness : ∀{A} → ST → Nat → CryptoExpr A → Set₁ where
  Return-ER   : ∀{A n st} (a : A) → EnoughRandomness st n (Return-FM a)
  Uniform-ER  : ∀{A n k st} 
              → {cont : BitVec n → CryptoExpr A}
              → ((v : BitVec n) → EnoughRandomness st k (cont v))
              → EnoughRandomness st (n + k) (Invoke-FM (Uniform n) cont)
  GetState-ER : ∀{A n st} 
              → {cont : ST → CryptoExpr A}
              → (er : EnoughRandomness st n (cont st))
              → EnoughRandomness st n (Invoke-FM GetState cont)
  SetState-ER : ∀{A n st st′} 
              → {cont : ⊤ → CryptoExpr A}
              → (er : EnoughRandomness st′ n (cont tt))
              → EnoughRandomness st n (Invoke-FM (SetState st′) cont)

postulate
  Weaken-ER : ∀{A n k st} → (n ≤ k) → {ce : CryptoExpr A}
            → EnoughRandomness st n ce
            → EnoughRandomness st k ce

get-final-state-fun : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → ST
get-final-state-fun st (Return-FM _) (Return-ER _) v = st
get-final-state-fun st (Invoke-FM (Uniform n) cont) (Uniform-ER er) v with vsplit n v
... | l , r = get-final-state-fun st (cont l) (er l) r
get-final-state-fun st (Invoke-FM  GetState cont) (GetState-ER er) v = get-final-state-fun st (cont st) er v
get-final-state-fun _  (Invoke-FM (SetState st′) cont) (SetState-ER er) v = get-final-state-fun st′ (cont tt) er v

get-randomness′-Sound : ∀{A} st (ce : CryptoExpr A) → EnoughRandomness st (get-randomness′ st ce) ce
get-randomness′-Sound st (Return-FM a) = Return-ER a
get-randomness′-Sound st (Invoke-FM (Uniform n) cont) = Uniform-ER λ v → Weaken-ER (maximumOf-Max _ v) (get-randomness′-Sound st (cont v))
get-randomness′-Sound st (Invoke-FM  GetState cont) = GetState-ER (get-randomness′-Sound st (cont st))
get-randomness′-Sound st (Invoke-FM (SetState st′) cont) = SetState-ER (get-randomness′-Sound st′ (cont tt)) 

get-result-fun : ∀{A k} st (ce : CryptoExpr A) → EnoughRandomness st k ce → BitVec k → A
get-result-fun st (Return-FM a) er v = a
get-result-fun st (Invoke-FM (Uniform n) cont) (Uniform-ER er) v with vsplit n v
... | l , r = get-result-fun st (cont l) (er l) r 
get-result-fun st (Invoke-FM  GetState cont) (GetState-ER er) v
  = get-result-fun st (cont st) er v
get-result-fun st (Invoke-FM (SetState st′) cont) (SetState-ER er) v
  = get-result-fun st′ (cont tt) er v

canonic-form : ∀{A} → CryptoExpr A → CryptoExpr A
canonic-form ce = Invoke-FM GetState λ st →
                  Invoke-FM (Uniform (get-randomness′ st ce)) λ v →
                  Invoke-FM (SetState (get-final-state-fun st ce (get-randomness′-Sound st ce) v)) λ _ → 
                  Return-FM (get-result-fun st ce (get-randomness′-Sound st ce) v)
