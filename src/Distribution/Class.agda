module Distribution.Class where

open import ThesisPrelude
open import Probability.Class
open import Utility.Vector
open import Algebra.Function

record DistMonad (D : Set → Set) : Set₁ where
  infix 4 _≡D_
  field
    probability : Set
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A}{{_ : Eq A}} → D A → A → probability
    _≡D_ : ∀{A}{{_ : Eq A}} → D A → D A → Set
    overlap {{probability-super}} : Probability probability
    overlap {{monad-super}} : Monad D
  open Probability probability-super
  coin : D Bool
  coin = fmap head (uniform 1)

  bounded-dist-diff : ∀{A}{{_ : Eq A}} → D A → D A → probability → Set
  bounded-dist-diff D₁ D₂ ε = ∀ a → bounded-diff (sample D₁ a) (sample D₂ a) ε 
