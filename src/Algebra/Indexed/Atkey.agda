module Algebra.Indexed.Atkey where

open import ThesisPrelude

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data StrongAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set (l ⊔ l′) where
  StrongV : (a : A){s : S} → (hip : s ≡ f a) → StrongAtkey A f s

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s
