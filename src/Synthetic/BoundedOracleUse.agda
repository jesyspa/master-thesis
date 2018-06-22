{-# OPTIONS --type-in-type #-}
open import Synthetic.CryptoState
module Synthetic.BoundedOracleUse (CS : CryptoState) where

open import ThesisPrelude
open import Synthetic.CryptoExpr CS
open import Synthetic.CommandStructure
open import Synthetic.Enumeration
open FM
open import Utility.Vector.Definition
open import Utility.List.Elem.Definition
open import Probability.Class

open CryptoState CS

data BoundedOracleUse : {A : Set} → Bool → Nat → CryptoExpr A → Set₁ where
  ReturnBOU      : ∀{A} b k (a : A) → BoundedOracleUse b k (Return-FM a)
  UniformBOU     : ∀{A} b k n
                 → (cont : BitVec n → CryptoExpr A)
                 → (∀ v → BoundedOracleUse b k (cont v))
                 → BoundedOracleUse b k (Invoke-FM (Uniform n) cont)
  GetAdvStateBOU : ∀{A} b k (cont : AdvState → CryptoExpr A)
                 → (∀ st → BoundedOracleUse b k (cont st))
                 → BoundedOracleUse b k (Invoke-FM GetAdvState cont)
  SetAdvStateBOU : ∀{A} b k st (ce : CryptoExpr A)
                 → BoundedOracleUse b k ce
                 → BoundedOracleUse b k (Invoke-FM (SetAdvState st) (const ce))
  InitOracleBOU  : ∀{A} k st (ce : CryptoExpr A)
                 → BoundedOracleUse false k ce
                 → BoundedOracleUse true k (Invoke-FM (InitOracle st) (const ce))
  CallOracleBOU  : ∀{A} b k arg (cont : OracleResult → CryptoExpr A)
                 → (∀ r → BoundedOracleUse b k (cont r))
                 → BoundedOracleUse b (suc k) (Invoke-FM (CallOracle arg) cont)

open Enumeration {{...}}

all : List Bool → Bool
all = foldr _&&_ true

all-Sound-lem : ∀{A}
              → (xs : List A)
              → (P : A → Bool)
              → IsTrue (all (map P xs))
              → ∀ a → (a ∈ xs) → IsTrue (P a)
all-Sound-lem [] P pf a ()
all-Sound-lem (x ∷ xs) P pf a el with P x | graphAt P x
all-Sound-lem (x ∷ xs) P () a el | false | ingraph eq
all-Sound-lem (x ∷ xs) P pf .x (here .x .xs)        | true | ingraph eq rewrite eq = true
all-Sound-lem (x ∷ xs) P pf  a (there .a .x .xs el) | true | ingraph eq = all-Sound-lem xs P pf a el

all-Sound : ∀{A}{{_ : Enumeration A}}
          → (P : A → Bool)
          → IsTrue (all (map P Enumerate))
          → ∀ a → IsTrue (P a)
all-Sound P pf a = all-Sound-lem Enumerate P pf a (EnumerateComplete a)

module _ {{_ : Enumeration AdvState}}
         {{_ : Enumeration OracleResult}}
         {{_ : ∀{n} → Enumeration (BitVec n)}} where
  check-BOU? : ∀{A} → Bool → Nat → (CryptoExpr A) → Bool
  check-BOU? b      k  (Return-FM a) = true
  check-BOU? b      k  (Invoke-FM (Uniform n) cont)      = all (map (λ v → check-BOU? b k (cont v)) Enumerate) 
  check-BOU? b      k  (Invoke-FM  GetAdvState cont)     = all (map (λ v → check-BOU? b k (cont v)) Enumerate)
  check-BOU? b      k  (Invoke-FM (SetAdvState st) cont) = check-BOU? b k (cont tt)
  check-BOU? false  k  (Invoke-FM (InitOracle st) cont)  = false
  check-BOU? true   k  (Invoke-FM (InitOracle st) cont)  = check-BOU? false k (cont tt)
  check-BOU? b zero    (Invoke-FM (CallOracle arg) cont) = false
  check-BOU? b (suc k) (Invoke-FM (CallOracle arg) cont) = all (map (λ v → check-BOU? b k (cont v)) Enumerate)
  
  check-BOU-Sound : ∀{A} b k → (ce : CryptoExpr A) → IsTrue (check-BOU? b k ce) → BoundedOracleUse b k ce
  check-BOU-Sound b k (Return-FM a) pf = ReturnBOU b k a
  check-BOU-Sound b k (Invoke-FM (Uniform n) cont) pf
    = UniformBOU b k n cont λ v → check-BOU-Sound b k (cont v) (all-Sound _ pf v)
  check-BOU-Sound b k (Invoke-FM  GetAdvState cont) pf
    = GetAdvStateBOU b k cont λ st → check-BOU-Sound b k (cont st) (all-Sound _ pf st)
  check-BOU-Sound b k (Invoke-FM (SetAdvState st) cont) pf
    = SetAdvStateBOU b k st (cont tt) (check-BOU-Sound b k (cont tt) pf)
  check-BOU-Sound false k (Invoke-FM (InitOracle st) cont) ()
  check-BOU-Sound true  k (Invoke-FM (InitOracle st) cont) pf
    = InitOracleBOU k st (cont tt) (check-BOU-Sound false k (cont tt) pf)
  check-BOU-Sound b zero    (Invoke-FM (CallOracle arg) cont) ()
  check-BOU-Sound b (suc k) (Invoke-FM (CallOracle arg) cont) pf
    = CallOracleBOU b k arg cont λ r → check-BOU-Sound b k (cont r) (all-Sound _ pf r)
