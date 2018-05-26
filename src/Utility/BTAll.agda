module Utility.BTAll where

open import ThesisPrelude

data BTree {l}(A : Set l) : Set l where
  Leaf : A → BTree A
  Split : (l r : BTree A) → BTree A

infixr 5 _▵_
data BTAll {l l′}{A : Set l}(P : A → Set l′) : BTree A → Set l′ where
  leaf : ∀{a} → P a → BTAll P (Leaf a)
  _▵_ : ∀{l r} → BTAll P l → BTAll P r → BTAll P (Split l r)

BTAll′ : ∀{l} → BTree (Set l) → Set l
BTAll′ t = BTAll id t
