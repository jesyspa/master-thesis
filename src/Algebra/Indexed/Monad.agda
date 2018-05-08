open import ThesisPrelude
module Algebra.Indexed.Monad {l l′}{S : Set l}(M : (S → Set l′) → S → Set l′) where

record IxMonad : Set (lsuc l′ ⊔ l) where
  infixl 1 _>>=ⁱ_
  field
    fmapⁱ : ∀{A A′ s} → (∀{s′} → A s′ → A′ s′) → M A s → M A′ s
    returnⁱ : ∀{A s} → A s → M A s
    _>>=ⁱ_ : ∀{A B s} → M A s → (∀{s′} → A s′ → M B s′) → M B s

data Atkey {l l′}{S : Set l}(A : Set l′): S → S → Set l′ where
  V : ∀{s} → A → Atkey A s s

data DepAtkey {l l′}{S : Set l}(A : Set l′)(f : A → S) : S → Set l′ where
  DepV : (a : A) → DepAtkey A f (f a)

data MagicAtkey {l l′}{S S′ : Set l}(A : Set l′)(st : S → S′)(f : A → S′) : S → Set (l′ ⊔ l) where
  MagicV : ∀{s} → (a : A) → f a ≡ st s → MagicAtkey A st f s
