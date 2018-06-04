module Utility.BTAll where

open import ThesisPrelude

infixr 5 _△_
data BTree {l}(A : Set l) : Set l where
  Leaf : A → BTree A
  _△_ : (l r : BTree A) → BTree A

infixr 5 _▵_
data BTAll {l l′}{A : Set l}(P : A → Set l′) : BTree A → Set l′ where
  leaf : ∀{a} → P a → BTAll P (Leaf a)
  _▵_ : ∀{l r} → BTAll P l → BTAll P r → BTAll P (l △ r)

BTAll′ : ∀{l} → BTree (Set l) → Set l
BTAll′ t = BTAll id t

fst-BT′ : ∀{l}{A B : BTree (Set l)}
        → BTAll′ (A △ B) → BTAll′ A
fst-BT′ (r ▵ _) = r

first-BT′ : ∀{l}{A B C : BTree (Set l)}(f : BTAll′ A → BTAll′ C)
          → BTAll′ (A △ B) → BTAll′ (C △ B)
first-BT′ f (a ▵ b) = f a ▵ b

snd-BT′ : ∀{l}{A B : BTree (Set l)}
        → BTAll′ (A △ B) → BTAll′ B
snd-BT′ (_ ▵ r) = r

second-BT′ : ∀{l}{A B C : BTree (Set l)}(f : BTAll′ B → BTAll′ C)
           → BTAll′ (A △ B) → BTAll′ (A △ C)
second-BT′ f (a ▵ b) = a ▵ f b

infixr 3 _***-BT′_ 
_***-BT′_ : ∀{l}{A B C D : BTree (Set l)}(f : BTAll′ A → BTAll′ C)(g : BTAll′ B → BTAll′ D)
          → BTAll′ (A △ B) → BTAll′ (C △ D)
_***-BT′_ f g  (x ▵ y) = f x ▵ g y
