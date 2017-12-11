module Preorder where

open import MyPrelude

record Preorder (A : Set) : Set₁ where
  infix 4 _≤_
  field
    _≤_ : A → A → Set
    ≤-refl : ∀ a → a ≤ a
    ≤-trans : ∀ a b c → a ≤ b → b ≤ c → a ≤ c

open Preorder {{...}} public

infix 1 _[_]∎
infixr 0 leqReasoningStep

syntax leqReasoningStep x q p = x ≤⟨ p ⟩ q
leqReasoningStep : ∀{A} → {{_ : Preorder A}} → {a b c : A} → a ≤ b → b ≤ c → a ≤ c
leqReasoningStep {A} {{P}} {a} {b} {c} p q = ≤-trans a b c p q

_[_]∎ : ∀{A} → (a : A) → (P : Preorder A) → _≤_ {{P}} a a
_[_]∎ {A} a P = ≤-refl {{P}} a
