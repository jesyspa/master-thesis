module Synthetic.CryptoExpr where

open import ThesisPrelude
open import Utility.Vector.Definition
open import Probability.Class

record CryptoState : Set₁ where
  field
    AdvState     : Set
    OracleState  : Set
    OracleArg    : Set
    OracleResult : Set

module _ CS where
  open CryptoState CS
  data CryptoExpr : (S : Set) → Set where
    Return      : ∀{A} → A                                           → CryptoExpr A
    Uniform     : ∀{A} → (n : Nat)   → (BitVec n     → CryptoExpr A) → CryptoExpr A
    GetAdvState : ∀{A}               → (AdvState     → CryptoExpr A) → CryptoExpr A
    SetAdvState : ∀{A} → AdvState    →                 CryptoExpr A  → CryptoExpr A
    InitOracle  : ∀{A} → OracleState →                 CryptoExpr A  → CryptoExpr A
    CallOracle  : ∀{A} → OracleArg   → (OracleResult → CryptoExpr A) → CryptoExpr A

  postulate
    M : Set → Set
    instance
      FunctorM     : Functor M
      ApplicativeM : Applicative M
      MonadM       : Monad M
    uniform : (n : Nat) → M (BitVec n)
    putState : AdvState × OracleState → M ⊤
    getState : M (AdvState × OracleState)

  record OracleImpl : Set₁ where
    field
      InitImpl : OracleState → M ⊤
      CallImpl : OracleArg → M OracleResult
  
  eval-CE : ∀{A} → CryptoExpr A → M A
  eval-CE ce = {!!}

  postulate
    _≡D_ : ∀{A} → M A → M A → Set
    
