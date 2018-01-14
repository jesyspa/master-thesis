module Distribution.Class where

open import ThesisPrelude
open import Probability.Class
open import Utility.Vector.BitVec
open import Algebra.Function

record DistMonad (D : Set → Set) : Set₁ where
  infix 4 _≡D_
  field
    probability : Set
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A} → {{_ : Eq A}} → D A → A → probability
    _≡D_ : ∀{A} → {{_ : Eq A}} → D A → D A → Set
    overlap {{carrier-structure}} : Probability probability
    overlap {{monad-structure}} : Monad D

