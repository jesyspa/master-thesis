module Algebra.Indexed.Atkey where

open import ThesisPrelude
open import Algebra.Relation

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

-- Equivalent to DepAtkey, but nicer to work with.
data StrongAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set (l ⊔ l′) where
  StrongV : (a : A){s : S} → (hip : s ≡ f a) → StrongAtkey A f s

rewrap-StrongAtkey : ∀{l l′}{S S′ : Set l}{A : Set l′}{f : A → S}(h : S → S′){s : S}
                   → StrongAtkey A f s → StrongAtkey A (h ∘′ f) (h s)
rewrap-StrongAtkey h (StrongV a refl) = StrongV a refl

strengthen-Atkey : ∀{l l′}{S : Set l}{A : Set l′}{s s′ : S}
                 → Atkey A s s′ → StrongAtkey A (const s) s′
strengthen-Atkey (V x) = StrongV x refl

-- Somehow, this is equivalent to StrongAtkey.
KanAtkey : {S : Set}(A : Set)(f : A → S) → S → Set
KanAtkey A f s = Lan (const A) s
  where
    open import Algebra.KanExtension f 

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s

data RelAtkey {S S′ : Set}(R : Relation S S′) : S → S′ → Set where
  RelV : ∀{s s′} → R s s′ → RelAtkey R s s′

data DepRelAtkey {S S′ : Set}(R : Relation S S′)(A : Set)(f : A → S) : S′ → Set where
  DepRelV : ∀ a {s′} → R (f a) s′ → DepRelAtkey R A f s′
