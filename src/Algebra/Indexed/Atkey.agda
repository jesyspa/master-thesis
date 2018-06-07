module Algebra.Indexed.Atkey where

open import ThesisPrelude

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data StrongAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set (l ⊔ l′) where
  StrongV : (a : A){s : S} → (hip : s ≡ f a) → StrongAtkey A f s

rewrap-StrongAtkey : ∀{l l′}{S S′ : Set l}{A : Set l′}{f : A → S}(h : S → S′){s : S}
                   → StrongAtkey A f s → StrongAtkey A (h ∘′ f) (h s)
rewrap-StrongAtkey h (StrongV a refl) = StrongV a refl

strengthen-Atkey : ∀{l l′}{S : Set l}{A : Set l′}{s s′ : S}
                 → Atkey A s s′ → StrongAtkey A (const s) s′
strengthen-Atkey (V x) = StrongV x refl

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s
