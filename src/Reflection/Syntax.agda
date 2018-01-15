module Reflection.Syntax where

open import ThesisPrelude
open import Utility.Vector.BitVec
open import Utility.List.Elem

data Ty : Set where
  bitvec : Nat → Ty
  -- TODO: figure out what types we want to support.

postulate
  evalType : Ty → Set
  
Ctx : Set
Ctx = List Ty


data CryptoAgdaExpr (Var : Ty → Set) : Ctx → Ty → Set₁ where
  var-CAE : ∀{Γ A} → Var A → CryptoAgdaExpr Var Γ A
  return-CAE : ∀{A} → evalType A → CryptoAgdaExpr Var [] A
  bind-CAE : ∀{Γ A B} → CryptoAgdaExpr Var Γ A → CryptoAgdaExpr Var (A ∷ Γ) B → CryptoAgdaExpr Var Γ B
  uniform-CAE : ∀ n → CryptoAgdaExpr Var [] (bitvec n)
  fmap-CAE : ∀{Γ A B} → (evalType A → evalType B) → CryptoAgdaExpr Var Γ A → CryptoAgdaExpr Var Γ B
  lam-CAE : ∀{Γ A B} → (Var A → CryptoAgdaExpr Var Γ B) → CryptoAgdaExpr Var (A ∷ Γ) B
  weaken-CAE : ∀{Γ A B} → CryptoAgdaExpr Var Γ A → evalType B → CryptoAgdaExpr Var (B ∷ Γ) A
