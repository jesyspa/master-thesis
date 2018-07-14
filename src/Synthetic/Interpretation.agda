{-# OPTIONS --type-in-type #-}
open import Probability.Class
open import Probability.PropsClass
open import ThesisPrelude
module Synthetic.Interpretation ST Q {{_ : Probability Q}}{{_ : Eq ST}} where

open import Synthetic.CommandStructure
open import Synthetic.CryptoExpr ST
open import Utility.Vector.Definition

open FM CryptoExprCS
open CommandStructure

postulate
  M : Set → Set
  instance
    FunctorM     : Functor M
    ApplicativeM : Applicative M
    MonadM       : Monad M
  uniform : (n : Nat) → M (BitVec n)
  setState : ST → M ⊤
  getState : M ST

  sample : ∀{A}{{_ : Eq A}} → ST → A → M A → Q

module _ {A} where
  _≡D_ : M A → M A → Set
  m₁ ≡D m₂ = ∀{{_ : Eq A}} st a → sample st a m₁ ≡ sample st a m₂

{-
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


-}
