module Algebra.Indexed.Atkey where

open import ThesisPrelude
open import Algebra.Relation

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data StrongAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set (l ⊔ l′) where
  StrongV : (a : A){s : S} → (hip : s ≡ f a) → StrongAtkey A f s

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s

data RelAtkey {S S′ : Set}(R : Relation S S′) : S → S′ → Set where
  RelV : ∀{s s′} → R s s′ → RelAtkey R s s′

data DepRelAtkey {S S′ : Set}(R : Relation S S′)(A : Set)(f : A → S) : S′ → Set where
  DepRelV : ∀ a {s′} → R (f a) s′ → DepRelAtkey R A f s′
