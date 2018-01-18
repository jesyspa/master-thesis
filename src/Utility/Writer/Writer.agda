open import ThesisPrelude using (Monoid)
module Utility.Writer.Writer {l} (Q : Set l) {{QM : Monoid Q}} where

open import ThesisPrelude
open import Utility.Product
open import Algebra.Monoid

Writer : Set l → Set l
Writer A = A × Q

mul-Writer : ∀{A} → Q → Writer A → Writer A
mul-Writer q = over-snd (_<>_ q)

instance
  FunctorWriter : Functor Writer
  FunctorWriter = record { fmap = over-fst }

ap-W : ∀{A B : Set l} → Writer (A → B) → Writer A → Writer B
ap-W (f , v₁) (a , v₂) = f a , v₁ <> v₂

pure-W : ∀{A : Set l} → A → Writer A
pure-W = rev-pair mempty

instance
  ApplicativeWriter : Applicative Writer
  ApplicativeWriter = record { pure = pure-W ; _<*>_ = ap-W }

bind-W : ∀{A B : Set l} → Writer A → (A → Writer B) → Writer B
bind-W (x , v) f with f x
... | y , w = y , v <> w

instance
  MonadWriter : Monad Writer
  MonadWriter = record { _>>=_ = bind-W ; super = ApplicativeWriter }

