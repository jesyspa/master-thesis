module Distribution.Class where

open import ThesisPrelude
open import Carrier.Class
open import Utility.BitVec
open import Algebra.Function
open import Algebra.Monad

record DistMonad (D : Set → Set) : Set₁ where
  infix 4 _≡D_
  field
    carrier : Set
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A} → {{_ : Eq A}} → D A → A → carrier
    _≡D_ : ∀{A} → {{_ : Eq A}} → D A → D A → Set
    overlap {{carrier-structure}} : Carrier carrier
    overlap {{monad-structure}} : Monad D

