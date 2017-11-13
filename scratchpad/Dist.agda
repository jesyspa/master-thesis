module Dist where

open import Data.Integer using (+_)
open import Data.Rational using (ℚ; _÷_)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

record Dist (A : Set) : Set where
  field
    density : A → ℚ
    support : (A → ℚ) → ℚ

returnDensity : ∀{A : Set} → {dec : Decidable (_≡_ {A = A})} → A → A → ℚ
returnDensity {dec = dec} x y with dec x y
...                            | Dec.yes _ = + 1 ÷ 1
...                            | Dec.no  _ = + 0 ÷ 1

returnSupport : ∀{A : Set} → A → (A → ℚ) → ℚ
returnSupport a f = f a

bindDensity : ∀{A B} → Dist A → (A → Dist B) → B → ℚ
bindDensity d f b = Dist.support d λ a → Dist.density (f a) b

bindSupport : ∀{A B} → Dist A → (A → Dist B) → (B → ℚ) → ℚ
bindSupport d f g = Dist.support d λ a → Dist.support (f a) g

returnD : ∀{A : Set} → {dec : Decidable (_≡_ {A = A})} → A → Dist A
returnD {dec = dec} a = record { density = returnDensity {dec = dec} a ; support = returnSupport a }

bindD : ∀{A B} → Dist A → (A → Dist B) → Dist B
bindD d f = record { density = bindDensity d f ; support = bindSupport d f }

{-
bindD : ∀{A B} → Dist A → (A → Dist B) → Dist B
c bindD f = ?

open import FreeMonad
open import Crypto
-}
