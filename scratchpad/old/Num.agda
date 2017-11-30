module Num where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 7 _*_
infixl 6 _+_
infix 4 _≤_ _≡_

data _≤_ : ℕ → ℕ →  Set where
  ≤-base : ∀{n} → zero ≤ n
  ≤-step : ∀{n m} → n ≤ m → succ n ≤ succ m

_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m = zero
succ n * m = m + n * m

data _≡_ {A : Set} : A → A → Set where
  refl : ∀{a} → a ≡ a

-- Some practice lemmas
transport : ∀{A B x y} → (f : A → B) → x ≡ y → f x ≡ f y
transport f refl = refl

≡-trans : ∀{A} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans refl refl = refl

≤-refl : ∀{a} → a ≤ a
≤-refl {zero} = ≤-base
≤-refl {succ a} = ≤-step ≤-refl

≤-antisym : ∀{a b} → a ≤ b → b ≤ a → a ≡ b
≤-antisym ≤-base ≤-base = refl
≤-antisym (≤-step p) (≤-step q) = transport succ (≤-antisym p q)

≤-trans : ∀{a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans {.zero} {b} {c} ≤-base _ = ≤-base
≤-trans {.(succ _)} {.(succ _)} {.(succ _)} (≤-step p) (≤-step q) = ≤-step (≤-trans p q)

+-monotone : ∀{a b} → a ≤ a + b
+-monotone {zero} = ≤-base
+-monotone {succ a} = ≤-step +-monotone

induction : {P : ℕ → Set} → {pz : P zero} → {ps : {a : ℕ} → P a → P (succ a)} → (n : ℕ) → P n
induction {P} {pz} {ps} zero = pz
induction {P} {pz} {ps} (succ n) = ps (induction {P} {pz} {ps} n)

+-zero-eq : ∀{a} → a ≡ a + zero
+-zero-eq {a} = induction {λ a' → a' ≡ a' + zero} {refl} {transport succ} a

+-one-eq : ∀{b} → succ b ≡ b + succ zero
+-one-eq {b} = induction {λ b' → succ b' ≡ b' + succ zero} {refl} {transport succ} b

+-succ-lem : ∀{a b} → succ (a + b) ≡ a + succ b
+-succ-lem {zero} {b} = refl
+-succ-lem {succ a} {b} = transport succ +-succ-lem

+-comm : ∀{a b} → a + b ≡ b + a
+-comm {zero} {b} = +-zero-eq
+-comm {succ a} {b} = {!   !}
