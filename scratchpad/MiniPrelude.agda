module MiniPrelude where

open import Prelude.Equality using (_≡_; refl; sym; _⟨≡⟩_; trans; cong; transport) public
open import Prelude.Nat using (Nat; suc; zero; _+N_) public
open import Numeric.Nat.Properties.Core using (add-inj₁; add-assoc; add-commute) public

data _≤N_ n m : Set where
  diff : ∀ k (eq : m ≡ k +N n) → n ≤N m

refl≤ : ∀ i → i ≤N i
refl≤ i = diff zero refl

trans≤ : ∀{i j k} → (q : j ≤N k) → (p : i ≤N j) → i ≤N k
trans≤ {i} (diff b eqb) (diff a eqa) rewrite eqb = diff (b +N a) (cong (_+N_ b) eqa ⟨≡⟩ add-assoc b a i)

postulate
  Nat≤-pi : ∀{i j} → (p q : i ≤N j) → p ≡ q
