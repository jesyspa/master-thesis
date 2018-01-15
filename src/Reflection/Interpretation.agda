module Reflection.Interpretation where

open import ThesisPrelude
open import Reflection.Syntax
open import Crypto.Syntax

evalContext : Ctx → Set
evalContext = foldr _×_ ⊤ ∘′ map evalType

data Var (A : Ty) : Set where
  ix : Nat → Var A 

-- I should be carrying around some kind of context?
eval : ∀{Γ A} → CryptoAgdaExpr Var Γ A → CryptoExpr (evalType A)
eval (var-CAE x) = {!!}
eval (return-CAE x) = returnCE x
eval (bind-CAE x y) = {!!}
eval (uniform-CAE n) = {!!}
eval (fmap-CAE x x₁) = {!!}
eval (lam-CAE x) = {!!}
eval (weaken-CAE x x₁) = {!!}
