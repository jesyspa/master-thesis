module Crypto.Syntax where

open import ThesisPrelude
open import Utility.Product
open import Utility.Sum
open import Utility.Vector.BitVec
open import Utility.Vector.Functions
open import Utility.List.Elem

OracleList : Set₁
OracleList = List (Set × Set)

data CryptoExpr : OracleList → OracleList → Set → Set → Set₁ where
  embed-CE : ∀{O A B} → (g : A → B) → CryptoExpr O O A B
  uniform-CE : ∀{O O′ A B} n → CryptoExpr O O′ (BitVec n × A) B → CryptoExpr O O′ A B
  addOracle-CE : ∀{O O′ O′′ A B C X Y}
               → CryptoExpr O O′ A ((X → Y) × B) → CryptoExpr ((X , Y) ∷ O′) O′′ B C
               → CryptoExpr O O′′ A C
  -- This is crazy. (But it works?)
  callOracle-CE : ∀{O O′ O′′ A B C X Y} (p : (X , Y) ∈ O)
                → CryptoExpr O O′ A (X × B) → CryptoExpr O′ O′′ (Y × B) C
                → CryptoExpr O O′′ A C
  -- The problem here is that semantically equivalent CryptoExprs can have different
  -- denotations this way due to a difference in the choice of B in addOracle and SetOracle.
  -- This makes sense, but means that certain equality results that we'd like to prove
  -- are no longer provable.  Really, I want some kind of setoid to reason in, and then
  -- show that valuations are equivalent up to that setoid.


fmap-CE : ∀{O O′ A B B′} → (B → B′) → CryptoExpr O O′ A B → CryptoExpr O O′ A B′
fmap-CE f (embed-CE g) = embed-CE λ z → f (g z)
fmap-CE f (uniform-CE n ce) = uniform-CE n $ fmap-CE f ce
fmap-CE f (addOracle-CE ce cf) = addOracle-CE ce $ fmap-CE f cf
fmap-CE f (callOracle-CE p ce cf) = callOracle-CE p ce $ fmap-CE f cf

cofmap-CE : ∀{O O′ A A′ B} → (A → A′) → CryptoExpr O O′ A′ B → CryptoExpr O O′ A B
cofmap-CE f (embed-CE g) = embed-CE λ z → g (f z)
cofmap-CE f (uniform-CE n ce) = uniform-CE n $ cofmap-CE (second f) ce
cofmap-CE f (addOracle-CE ce cf) = addOracle-CE (cofmap-CE f ce) cf
cofmap-CE f (callOracle-CE p ce cf) = callOracle-CE p (cofmap-CE f ce) cf

infixr 2 _>>>-CE_ 
_>>>-CE_ : ∀{O O′ O′′ A B C} → CryptoExpr O O′ A B → CryptoExpr O′ O′′ B C → CryptoExpr O O′′ A C
embed-CE g >>>-CE rhs = cofmap-CE g rhs
uniform-CE n lhs >>>-CE rhs = uniform-CE n $ lhs >>>-CE rhs
addOracle-CE lhs lhs′ >>>-CE rhs = addOracle-CE lhs $ lhs′ >>>-CE rhs
callOracle-CE p lhs lhs′ >>>-CE rhs = callOracle-CE p lhs $ lhs′ >>>-CE rhs

rev-first : ∀{l}{A A′ B : Set l} → A × A′ × B → A′ × A × B
rev-first (a , a′ , b) = (a′ , a , b)

reverse-CE : ∀{O A A′ B} → CryptoExpr O O (A × A′ × B) (A′ × A × B)
reverse-CE = embed-CE rev-first

first-CE : ∀{O O′ A B C} → CryptoExpr O O′ A B → CryptoExpr O O′ (A × C) (B × C)
first-CE (embed-CE g) = embed-CE $ first g
first-CE (uniform-CE n ce) = uniform-CE n $ cofmap-CE unassoc $ first-CE ce
first-CE (addOracle-CE ce cf) = addOracle-CE (fmap-CE assoc (first-CE ce)) (first-CE cf)
first-CE (callOracle-CE p ce cf) = callOracle-CE p (fmap-CE assoc $ first-CE ce) (cofmap-CE unassoc $ first-CE cf)

second-CE : ∀{O O′ A B C} → CryptoExpr O O′ A B → CryptoExpr O O′ (C × A) (C × B)
second-CE (embed-CE g) = embed-CE $ second g
second-CE (uniform-CE n ce) = uniform-CE n $ cofmap-CE rev-first $ second-CE ce
second-CE (addOracle-CE ce cf) = addOracle-CE (fmap-CE rev-first (second-CE ce)) (second-CE cf)
second-CE (callOracle-CE p ce cf) = callOracle-CE p (fmap-CE rev-first $ second-CE ce) (cofmap-CE rev-first $ second-CE cf)

attach-CE : ∀{O A B} → B → CryptoExpr O O A (B × A)
attach-CE c = embed-CE (_,_ c)

infixr 4 _***-CE_ _&&&-CE_
_***-CE_ : ∀{O A B A′ B′} → CryptoExpr O O A B → CryptoExpr O O A′ B′ → CryptoExpr O O (A × A′) (B × B′)
lhs ***-CE rhs = first-CE lhs >>>-CE second-CE rhs

_&&&-CE_ : ∀{O A B B′} → CryptoExpr O O A B → CryptoExpr O O A B′ → CryptoExpr O O A (B × B′)
lhs &&&-CE rhs = embed-CE diag >>>-CE lhs ***-CE rhs

distribute : ∀{l}{A B C : Set l} → B × Either A C → Either (B × A) (B × C)
distribute (b , left a) = left (b , a)
distribute (b , right c) = right (b , c)

undistribute : ∀{l}{A B C : Set l} → Either (B × A) (B × C) → B × Either A C
undistribute (left (b , a)) = b , left a
undistribute (right (b , c)) = b , right c

{- This definition of CryptoExpr does not support ArrowChoice: given a call to an oracle,
   if we instead get some other data we will not be able to create an X to call the oracle with.
left-CE : ∀{O O′ A B C} → CryptoExpr O O′ A B → CryptoExpr O O′ (Either A C) (Either B C)
left-CE (embed-CE g) = embed-CE (mapLeft g)
left-CE (uniform-CE n ce) = uniform-CE n $ embed-CE (mapRight snd ∘′ distribute) >>>-CE left-CE ce
left-CE (addOracle-CE g ce) = addOracle-CE g $ left-CE ce
left-CE (callOracle-CE p ce cf) = callOracle-CE p (fmap-CE {!!} {!!}) (cofmap-CE {!!} {!!})

right-CE : ∀{A B C} → CryptoExpr A B → CryptoExpr (Either C A) (Either C B)
right-CE (embed-CE g) = embed-CE (mapRight g)
right-CE (uniform-CE n ce) = uniform-CE n $ embed-CE undistribute >>>-CE right-CE ce

infixr 3 _+++-CE_ _|||-CE_
_+++-CE_ : ∀{A B A′ B′} → CryptoExpr A B → CryptoExpr A′ B′ → CryptoExpr (Either A A′) (Either B B′)
lhs +++-CE rhs = left-CE lhs >>>-CE right-CE rhs

_|||-CE_ : ∀{A A′ B} → CryptoExpr A B → CryptoExpr A′ B → CryptoExpr (Either A A′) B
lhs |||-CE rhs = lhs +++-CE rhs >>>-CE embed-CE codiag
-}

uniform-expr : ∀{O A} n → CryptoExpr O O A (BitVec n × A)
uniform-expr n = uniform-CE n $ embed-CE id

uniform-expr′ : ∀{O} n → CryptoExpr O O ⊤ (BitVec n)
uniform-expr′ n = uniform-expr n >>>-CE embed-CE fst

instance
  FunctorCryptoExpr : ∀{O O′ A} → Functor (CryptoExpr O O′ A)
  FunctorCryptoExpr = record { fmap = fmap-CE }

coin-expr : ∀{O A} → CryptoExpr O O A (Bool × A)
coin-expr = fmap (first head) (uniform-expr 1)

coin-expr′ : ∀{O} → CryptoExpr O O ⊤ Bool
coin-expr′ = coin-expr >>>-CE embed-CE fst

