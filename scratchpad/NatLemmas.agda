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
