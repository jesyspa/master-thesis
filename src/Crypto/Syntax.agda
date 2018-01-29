module Crypto.Syntax where

open import ThesisPrelude
open import Utility.Product
open import Utility.Sum
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

infixr 2 _>>>-CE_ 
_>>>-CE_ : ∀{A B C} → CryptoExpr A B → CryptoExpr B C → CryptoExpr A C
embed-CE g >>>-CE rhs = cofmap-CE g rhs
uniform-CE n lhs >>>-CE rhs = uniform-CE n $ lhs >>>-CE rhs

first-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (A × C) (B × C)
first-CE (embed-CE g) = embed-CE $ first g
first-CE (uniform-CE n ce) = uniform-CE n $ cofmap-CE unassoc $ first-CE ce

rev-first : ∀{l}{A A′ B : Set l} → A × A′ × B → A′ × A × B
rev-first (a , a′ , b) = (a′ , a , b)

reverse-CE : ∀{A A′ B} → CryptoExpr (A × A′ × B) (A′ × A × B)
reverse-CE = embed-CE rev-first

second-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (C × A) (C × B)
second-CE (embed-CE g) = embed-CE $ second g
second-CE (uniform-CE n ce) = uniform-CE n $ cofmap-CE rev-first $ second-CE ce

attach-CE : ∀{A B} → B → CryptoExpr A (B × A)
attach-CE c = embed-CE (_,_ c)

infixr 4 _***-CE_ _&&&-CE_
_***-CE_ : ∀{A B A′ B′} → CryptoExpr A B → CryptoExpr A′ B′ → CryptoExpr (A × A′) (B × B′)
lhs ***-CE rhs = first-CE lhs >>>-CE second-CE rhs

_&&&-CE_ : ∀{A B B′} → CryptoExpr A B → CryptoExpr A B′ → CryptoExpr A (B × B′)
lhs &&&-CE rhs = embed-CE diag >>>-CE lhs ***-CE rhs

distribute : ∀{l}{A B C : Set l} → B × Either A C → Either (B × A) C
distribute (b , left a) = left (b , a)
distribute (b , right c) = right c

left-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (Either A C) (Either B C)
left-CE (embed-CE g) = embed-CE (mapLeft g)
left-CE (uniform-CE n ce) = uniform-CE n $ embed-CE distribute >>>-CE left-CE ce

undistribute : ∀{l}{A B C : Set l} → B × Either C A → Either C (B × A)
undistribute (b , left c) = left c
undistribute (b , right a) = right (b , a)

right-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (Either C A) (Either C B)
right-CE (embed-CE g) = embed-CE (mapRight g)
right-CE (uniform-CE n ce) = uniform-CE n $ embed-CE undistribute >>>-CE right-CE ce

infixr 3 _+++-CE_ _|||-CE_
_+++-CE_ : ∀{A B A′ B′} → CryptoExpr A B → CryptoExpr A′ B′ → CryptoExpr (Either A A′) (Either B B′)
lhs +++-CE rhs = left-CE lhs >>>-CE right-CE rhs

_|||-CE_ : ∀{A A′ B} → CryptoExpr A B → CryptoExpr A′ B → CryptoExpr (Either A A′) B
lhs |||-CE rhs = lhs +++-CE rhs >>>-CE embed-CE codiag

uniform-expr : ∀{A} n → CryptoExpr A (BitVec n × A)
uniform-expr n = uniform-CE n $ embed-CE id

uniform-expr′ : ∀ n → CryptoExpr ⊤ (BitVec n)
uniform-expr′ n = uniform-expr n >>>-CE embed-CE fst

instance
  FunctorCryptoExpr : ∀{A} → Functor (CryptoExpr A)
  FunctorCryptoExpr = record { fmap = fmap-CE }

coin-expr : ∀{A} → CryptoExpr A (Bool × A)
coin-expr = fmap (first head) (uniform-expr 1)

coin-expr′ : CryptoExpr ⊤ Bool
coin-expr′ = coin-expr >>>-CE embed-CE fst

