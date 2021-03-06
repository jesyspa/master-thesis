module Algebra.FunExt where

open import ThesisPrelude

postulate
  fun-ext : ∀{l l′} {A : Set l} {B : Set l′} (f g : A → B)
          → (∀ a → f a ≡ g a)
          → f ≡ g

  dep-fun-ext : ∀{l l′}{A : Set l}{B : A → Set l′}(f g : (a : A) → B a)
              → (∀ a → f a ≡ g a)
              → f ≡ g
