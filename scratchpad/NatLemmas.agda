{-# OPTIONS --allow-unsolved-metas #-}
module NatLemmas where

open import MyPrelude

nat-add-zero-lem : (m : Nat) → m ≡ m +N 0
nat-add-zero-lem zero = refl
nat-add-zero-lem (suc m) = cong suc (nat-add-zero-lem m)

nat-mul-one-lem : (n : Nat) → n ≡ 1 *N n 
nat-mul-one-lem = nat-add-zero-lem

nat-+0n-lem : (k n : Nat) → k ≡ k +N 0 *N n
nat-+0n-lem k n = nat-add-zero-lem k

mul2-lem : (n : Nat) → n +N n ≡ 2 *N n
mul2-lem n = cong (λ x → n +N x) (nat-add-zero-lem n)

nat-assoc-lem : (k n m : Nat) → k +N (n +N m) ≡ (k +N n) +N m
nat-assoc-lem zero n m = refl
nat-assoc-lem (suc k) n m = cong suc (nat-assoc-lem k n m)

nat-commute-helper : (k n : Nat) → suc (k +N n) ≡ k +N suc n 
nat-commute-helper zero n = refl
nat-commute-helper (suc k) n = cong suc (nat-commute-helper k n)

nat-commute-lem : (k n : Nat) → k +N n ≡ n +N k
nat-commute-lem zero n = nat-add-zero-lem n
-- (suc k) +N n = suc (k +N n) = suc (n +N k) = (suc n +N k)
nat-commute-lem (suc k) n =
  suc (k +N n) 
    ≡⟨ cong suc (nat-commute-lem k n) ⟩
  suc (n +N k)
    ≡⟨ nat-commute-helper n k ⟩
  n +N suc k
  ∎

nat-dist-lem : (k n m : Nat) → k *N n +N k *N m ≡ k *N (n +N m)
nat-dist-lem zero n m = refl
nat-dist-lem (suc k) n m =
  (n +N k *N n) +N (m +N k *N m)
    ≡⟨  sym (nat-assoc-lem n (k *N n) (m +N k *N m))  ⟩
  n +N (k *N n +N (m +N k *N m))
    ≡⟨ cong (λ x → n +N x) (nat-assoc-lem (k *N n) m (k *N m)) ⟩
  n +N ((k *N n +N m) +N k *N m)
    ≡⟨ cong (λ x → n +N (x +N k *N m)) (nat-commute-lem (k *N n) m) ⟩
  n +N ((m +N k *N n) +N k *N m)
    ≡⟨ nat-assoc-lem n (m +N k *N n) (k *N m) ⟩
  (n +N (m +N k *N n)) +N k *N m
    ≡⟨ cong (λ x → x +N k *N m) (nat-assoc-lem n m (k *N n)) ⟩
  ((n +N m) +N k *N n) +N k *N m
    ≡⟨ sym (nat-assoc-lem (n +N m) (k *N n) (k *N m)) ⟩
  (n +N m) +N (k *N n +N k *N m)
    ≡⟨ cong (λ x → (n +N m) +N x) (nat-dist-lem k n m) ⟩
  (n +N m) +N (k *N (n +N m))
  ∎
