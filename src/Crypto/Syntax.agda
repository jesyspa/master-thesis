module Crypto.Syntax where

open import ThesisPrelude
open import Utility.List
open import Utility.List.SubList.Definition
open import Utility.Vector.BitVec
open import Utility.Vector.Functions

OracleList : Set₁
OracleList = List (Set × Set)

Oracle : (In Out : Set)(O : OracleList) → Set
Oracle In Out O = (In , Out) ∈ O

data CryptoExpr : OracleList → OracleList → Set → Set₁ where
  returnCE : ∀{O A} → A → CryptoExpr O O A
  uniformCE : ∀{O O′ A} n → (BitVec n → CryptoExpr O O′ A) → CryptoExpr O O′ A
  callOracleCE : ∀{O O′ X Y A} → (X , Y) ∈ O → X → (Y → CryptoExpr O O′ A) → CryptoExpr O O′ A
  addOracleCE : ∀{O O′ X Y A} → (X → Y) → CryptoExpr ((X , Y) ∷ O) O′ A → CryptoExpr O O′ A

uniform-expr : ∀{O} n → CryptoExpr O O (BitVec n)
uniform-expr n = uniformCE n returnCE

callOracle : ∀{O X Y} → (X , Y) ∈ O → X → CryptoExpr O O Y
callOracle p x = callOracleCE p x returnCE

addOracle : ∀{O X Y} → (X → Y) → CryptoExpr O ((X , Y) ∷ O) (Oracle X Y ((X , Y) ∷ O))
addOracle f = addOracleCE f (returnCE (here _ _))

fmap-CE : ∀{O O′ A B} → (A → B) → CryptoExpr O O′ A → CryptoExpr O O′ B
fmap-CE f (returnCE a) = returnCE (f a)
fmap-CE f (uniformCE n cont) = uniformCE n (λ z → fmap-CE f (cont z))
fmap-CE f (callOracleCE p x cont) = callOracleCE p x (λ z → fmap-CE f (cont z))
fmap-CE f (addOracleCE g ce) = addOracleCE g (fmap-CE f ce)

instance
  FunctorCryptoExpr : ∀{O O′} → Functor (CryptoExpr O O′)
  FunctorCryptoExpr = record { fmap = fmap-CE }

coin-expr : ∀{O} → CryptoExpr O O Bool
coin-expr = fmap head (uniform-expr 1)

bind-CE : ∀{O O′ O′′ A B} → CryptoExpr O O′ A → (A → CryptoExpr O′ O′′ B) → CryptoExpr O O′′ B
bind-CE (returnCE a) f = f a
bind-CE (uniformCE n cont) f = uniformCE n (λ z → bind-CE (cont z) f)
bind-CE (callOracleCE p a cont) f = callOracleCE p a (λ z → bind-CE (cont z) f)
bind-CE (addOracleCE g ce) f = addOracleCE g (bind-CE ce f)

infixr 1 _>>=ᴵ_
_>>=ᴵ_ = bind-CE

returnᴵ : ∀{O A} → A → CryptoExpr O O A
returnᴵ = returnCE
