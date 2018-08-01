module Utility.Vector.Functions where

open import ThesisPrelude
open import Utility.Num

vall : ∀{n} → Vec Bool n → Bool
vall = vfoldr _&&_ true

vzip : ∀{l} {A B : Set l} {n} → (A → A → B) → (xs ys : Vec A n) → Vec B n
vzip f [] [] = []
vzip f (x ∷ xs) (y ∷ ys) = f x y ∷ vzip f xs ys

head : ∀{l} {A : Set l} {n} → Vec A (suc n) → A
head (x ∷ _) = x

head1 : ∀{l} {A : Set l} → Vec A 1 → A
head1 = head {n = zero}

vconcat : ∀{l}{A : Set l}{n k} → Vec A n → Vec A k → Vec A (n + k)
vconcat [] ys = ys
vconcat (x ∷ xs) ys = x ∷ vconcat xs ys

vtake : ∀{l}{A : Set l} n {k} → Vec A (n + k) → Vec A n
vtake zero v = []
vtake (suc n) (x ∷ v) = x ∷ vtake n v

vtake′ : ∀{l}{A : Set l} n {k} → n ≤ k → Vec A k → Vec A n
vtake′ n {k} (diff i eq) v = vtake n (transport (Vec _) eq′ v)
  where eq′ : k ≡ n + i
        eq′ = suc-Inj eq ⟨≡⟩ auto

vsplit : ∀{l}{A : Set l} n {k} → Vec A (n + k) → Vec A n × Vec A k
vsplit zero xs = [] , xs
vsplit (suc n) (x ∷ xs) with vsplit n xs
...| l , r = x ∷ l , r

vsplit′ : ∀{l}{A : Set l}{n k} → (le : n ≤ k) → Vec A k → Vec A n × Vec A (≤N-get-diff le)
vsplit′ (diff k eq) xs rewrite ≤N-get-eq (diff k eq) = vsplit _ xs
