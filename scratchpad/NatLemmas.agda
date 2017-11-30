module NatLemmas where

open import MyPrelude

nat-one-lem : {n : Nat} → 1 * n ≡ n
nat-one-lem {n} = 1 * n ≡⟨ refl ⟩ n + 0 ≡⟨ nat-add-zero ⟩ n ∎
  where
  nat-add-zero : {m : Nat} → m + 0 ≡ m
  nat-add-zero {zero} = refl
  nat-add-zero {suc m} = cong suc nat-add-zero
