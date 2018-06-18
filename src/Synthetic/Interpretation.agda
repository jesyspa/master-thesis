open import Synthetic.CryptoState
module Synthetic.Implementation (CS : CryptoState)

open import ThesisPrelude
open import Synthetic.CryptoExpr CS

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
  eval-CEA : ∀{A} → CryptoExprAlg A (M A)
  ReturnF      eval-CEA a     = return a
  UniformF     eval-CEA n m   = uniform n >>= m
  GetAdvStateF eval-CEA m     = getAdvState >>= m
  SetAdvStateF eval-CEA st m  = setAdvState st >> m
  InitOracleF  eval-CEA st m  = InitImpl st >> m
  CallOracleF  eval-CEA arg m = CallImpl arg >>= m
  
  eval-CE : ∀{A} → CryptoExpr A → M A
  eval-CE = fold-CE eval-CEA
