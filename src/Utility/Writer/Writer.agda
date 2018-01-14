open import ThesisPrelude using (Monoid)
module Utility.Writer.Writer {l} (Q : Set l) {{QM : Monoid Q}} where

open import ThesisPrelude
open import Algebra.Monoid

Writer : Set l → Set l
Writer A = A × Q

fmap-W : ∀{A B : Set l} → (A → B) → Writer A → Writer B 
fmap-W f (a , q) = f a , q

make-W : ∀{A} → Q → A → Writer A
make-W q a = a , q

instance
  FunctorWriter : Functor Writer
  FunctorWriter = record { fmap = fmap-W }

ap-W : ∀{A B : Set l} → Writer (A → B) → Writer A → Writer B
ap-W (f , v₁) (a , v₂) = f a , v₁ <> v₂

pure-W : ∀{A : Set l} → A → Writer A
pure-W = make-W mempty

instance
  ApplicativeWriter : Applicative Writer
  ApplicativeWriter = record { pure = pure-W ; _<*>_ = ap-W }

bind-W : ∀{A B : Set l} → Writer A → (A → Writer B) → Writer B
bind-W (x , v) f with f x
... | y , w = y , v <> w

instance
  MonadWriter : Monad Writer
  MonadWriter = record { _>>=_ = bind-W ; super = ApplicativeWriter }

