module Crypto.Syntax where

open import ThesisPrelude
open import Utility.Product
open import Utility.Vector.BitVec
open import Utility.Vector.Functions

-- What if instead of modelling CryptoExpres as monads we model them as arrows?
-- The one constructor we (currently) need is merging uniform into existing states,
-- so A × BitVec n → B into A → B
-- Later we may want separate channels for oracles and for values.

data CryptoExpr : Set → Set → Set where
  embed-CE : ∀{A B} → (g : A → B) → CryptoExpr A B
  uniform-CE : ∀{A B} n → CryptoExpr (BitVec n × A) B → CryptoExpr A B

fmap-CE : ∀{A B B′} → (B → B′) → CryptoExpr A B → CryptoExpr A B′
fmap-CE f (embed-CE g) = embed-CE λ z → f (g z)
fmap-CE f (uniform-CE n ce) = uniform-CE n $ fmap-CE f ce

cofmap-CE : ∀{A A′ B} → (A → A′) → CryptoExpr A′ B → CryptoExpr A B
cofmap-CE f (embed-CE g) = embed-CE λ z → g (f z)
cofmap-CE f (uniform-CE n ce) = uniform-CE n $ cofmap-CE (second f) ce

infixr 1 _>>>-CE_ 
_>>>-CE_ : ∀{A B C} → CryptoExpr A B → CryptoExpr B C → CryptoExpr A C
embed-CE g >>>-CE rhs = cofmap-CE g rhs
uniform-CE n lhs >>>-CE rhs = uniform-CE n $ lhs >>>-CE rhs

first-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (A × C) (B × C)
first-CE (embed-CE g) = embed-CE $ first g
first-CE (uniform-CE n ce) = uniform-CE n $ cofmap-CE unassoc $ first-CE ce

second-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (C × A) (C × B)
second-CE ce = embed-CE (uncurry rev-pair) >>>-CE first-CE ce >>>-CE embed-CE (uncurry rev-pair)

attach-CE : ∀{A B} → B → CryptoExpr A (B × A)
attach-CE c = embed-CE (_,_ c)

forget-CE : ∀{A B} → CryptoExpr (B × A) A
forget-CE = embed-CE snd

infixr 3 _***-CE_
_***-CE_ : ∀{A B A′ B′} → CryptoExpr A B → CryptoExpr A′ B′ → CryptoExpr (A × A′) (B × B′)
lhs ***-CE rhs = first-CE lhs >>>-CE second-CE rhs

uniform-expr : ∀{A} n → CryptoExpr A (BitVec n × A)
uniform-expr n = uniform-CE n $ embed-CE id

instance
  FunctorCryptoExpr : ∀{A} → Functor (CryptoExpr A)
  FunctorCryptoExpr = record { fmap = fmap-CE }

coin-expr : ∀{A} → CryptoExpr A (Bool × A)
coin-expr = fmap (first head) (uniform-expr 1)

