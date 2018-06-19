{-# OPTIONS --type-in-type #-}
open import Synthetic.CryptoState
module Synthetic.Interpretation (CS : CryptoState) where

open import ThesisPrelude
open import Synthetic.CommandStructure
open import Synthetic.CryptoExpr CS
open import Utility.Vector.Definition

open CryptoState CS
open FM CryptoExprCS
open CommandStructure

postulate
  M : Set → Set
  instance
    FunctorM     : Functor M
    ApplicativeM : Applicative M
    MonadM       : Monad M
  uniform : (n : Nat) → M (BitVec n)
  setAdvState : AdvState → M ⊤
  getAdvState : M AdvState

record OracleImpl : Set₁ where
  field
    InitImpl : OracleInit → M ⊤
    CallImpl : OracleArg → M OracleResult

module _ (OI : OracleImpl) where
  open OracleImpl OI
  eval-Alg : MonadicCommandAlgebra M
  eval-Alg (Uniform n) = uniform n
  eval-Alg GetAdvState = getAdvState
  eval-Alg (SetAdvState st) = setAdvState st
  eval-Alg (InitOracle st) = InitImpl st
  eval-Alg (CallOracle arg) = CallImpl arg
  
  eval-CE : ∀{A} → CryptoExpr A → M A
  eval-CE = fold-monadic-algebra eval-Alg

