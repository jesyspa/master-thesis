module Distribution.Class where

open import ThesisPrelude
open import Probability.Class
open import Utility.Vector
open import Algebra.Function
open import Algebra.FiniteSet

record DistMonad (D : Set → Set) : Set₁ where
  field
    probability : Set
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A}{{_ : Eq A}} → D A → A → probability
    overlap {{probability-super}} : Probability probability
    overlap {{monad-super}} : Monad D
  open Probability probability-super
  coin : D Bool
  coin = fmap head (uniform 1)

  infix 4 _≡D_
  data _≡D_ {A} {{_ : Eq A}} : D A → D A → Set where
    sample-equiv : {da db : D A}
                 → ((a : A) → sample da a ≡ sample db a)
                 → da ≡D db

  sample-invariant : ∀ {A} {{_ : Eq A}} {D₁ D₂ : D A} → D₁ ≡D D₂ → (a : A) → sample D₁ a ≡ sample D₂ a
  sample-invariant (sample-equiv f) a = f a

  sample-invariant-at : ∀{A}{{_ : Eq A}}{D₁ D₂ : D A} → (a : A) → D₁ ≡D D₂ → sample D₁ a ≡ sample D₂ a
  sample-invariant-at = flip sample-invariant

  sample-diff : ∀{A}{{_ : Eq A}} → D A → D A → A → probability
  sample-diff D₁ D₂ a = abs (sample D₁ a - sample D₂ a)

  dist-diff : ∀{A}{{_ : FiniteSet A}} → D A → D A → probability
  dist-diff D₁ D₂ = sum (map (sample-diff D₁ D₂) ListEnumeration)
    where open UniqueListable {{...}}
          open Listable super-Enumeration

  bounded-dist-diff : ∀{A}{{_ : FiniteSet A}} → D A → D A → probability → Set
  bounded-dist-diff D₁ D₂ ε = dist-diff D₁ D₂ ≤ ε

