{-# OPTIONS --allow-unsolved-metas #-}
module NatLemmas where

open import MyPrelude

nat-add-zero : {m : Nat} → m + 0 ≡ m
nat-add-zero {zero} = refl
nat-add-zero {suc m} = cong suc nat-add-zero

nat-one-lem : {n : Nat} → 1 * n ≡ n
nat-one-lem {n} = 1 * n ≡⟨ refl ⟩ n + 0 ≡⟨ nat-add-zero ⟩ n ∎

add-lem : ∀{k n} → k + 0 * n ≡ k
add-lem {k} {n} =
  k + 0 * n
    ≡⟨ refl ⟩
  k + 0
    ≡⟨ nat-add-zero ⟩
  k
  ∎

mul2-lem : (n : Nat) → n + n ≡ 2 * n
mul2-lem n = cong (λ x → n + x) (sym nat-add-zero)

nat-assoc-lem : {k n m : Nat} → k + (n + m) ≡ (k + n) + m
nat-assoc-lem {zero} {n} {m} = refl
nat-assoc-lem {suc k} {n} {m} = cong suc (nat-assoc-lem {k})

nat-commute-helper : {k n : Nat} → suc (k + n) ≡ k + suc n 
nat-commute-helper {zero} {n} = refl
nat-commute-helper {suc k} {n} = cong suc (nat-commute-helper {k})

nat-commute-lem : {k n : Nat} → k + n ≡ n + k
nat-commute-lem {zero} {n} = sym nat-add-zero
-- (suc k) + n = suc (k + n) = suc (n + k) = (suc n + k)
nat-commute-lem {suc k} {n} =
  suc (k + n) 
    ≡⟨ cong suc (nat-commute-lem {k} {n}) ⟩
  suc (n + k)
    ≡⟨ nat-commute-helper {n} {k} ⟩
  n + suc k
  ∎

nat-dist-lem : (k n m : Nat) → k * n + k * m ≡ k * (n + m)
nat-dist-lem zero n m = refl
nat-dist-lem (suc k) n m =
  (n + k * n) + (m + k * m)
    ≡⟨  sym (nat-assoc-lem {n} {k * n} {m + k * m})  ⟩
  n + (k * n + (m + k * m))
    ≡⟨ cong (λ x → n + x) (nat-assoc-lem {k * n} {m} {k * m}) ⟩
  n + ((k * n + m) + k * m)
    ≡⟨ cong (λ x → n + (x + k * m)) (nat-commute-lem {k * n} {m}) ⟩
  n + ((m + k * n) + k * m)
    ≡⟨ nat-assoc-lem {n} {m + k * n} {k * m} ⟩
  (n + (m + k * n)) + k * m
    ≡⟨ cong (λ x → x + k * m) (nat-assoc-lem {n} {m} {k * n}) ⟩
  ((n + m) + k * n) + k * m
    ≡⟨ sym (nat-assoc-lem {n + m} {k * n} {k * m}) ⟩
  (n + m) + (k * n + k * m)
    ≡⟨ cong (λ x → (n + m) + x) (nat-dist-lem k n m) ⟩
  (n + m) + (k * (n + m))
  ∎
