open import Synthetic.CryptoState
module Synthetic.BoundOracleUse (CS : CryptoState) where

open import ThesisPrelude
open import Synthetic.CryptoExpr CS
open import Utility.Vector.Definition
open import Probability.Class

data BoundOracleUse : {A : Set} → Bool → Nat → CryptoExpr A → Set₁ where
  ReturnBOU      : ∀{A} b k (a : A) → BoundOracleUse b k (Return a)
  UniformBOU     : ∀{A} b k n
                 → (cont : BitVec n → CryptoExpr A)
                 → (∀ v → BoundOracleUse b k (cont v))
                 → BoundOracleUse b k (Uniform n cont)
  GetAdvStateBOU : ∀{A} b k (cont : AdvState → CryptoExpr A)
                 → (∀ st → BoundOracleUse b k (cont st))
                 → BoundOracleUse b k (GetAdvState cont)
  SetAdvStateBOU : ∀{A} b k st (ce : CryptoExpr A)
                 → BoundOracleUse b k ce
                 → BoundOracleUse b k (SetAdvState st ce)
  InitOracleBOU  : ∀{A} k st (ce : CryptoExpr A)
                 → BoundOracleUse false k ce
                 → BoundOracleUse true k (InitOracle st ce)
  CallOracleBOU  : ∀{A} b k arg (cont : OracleResult → CryptoExpr A)
                 → (∀ r → BoundOracleUse b k (cont r))
                 → BoundOracleUse b (suc k) (CallOracle arg cont)
