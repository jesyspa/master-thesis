module Distribution.Class where

open import ThesisPrelude
open import Probability.Class
open import Utility.Vector
open import Algebra.Function
open import Algebra.FiniteSet
open import Algebra.FiniteSetExtensions

record DistMonad (F : Set → Set) : Set₁ where
  field
    probability : Set
    uniform : ∀ n → F (BitVec n)
    sample : ∀{A}{{_ : Eq A}} → F A → A → probability
    overlap {{probability-super}} : Probability probability
    overlap {{monad-super}} : Monad F
  open Probability probability-super
  coin : F Bool
  coin = fmap head (uniform 1)

  infix 4 _≡D_
  data _≡D_ {A} {{_ : Eq A}} : F A → F A → Set where
    sample-equiv : {da db : F A}
                 → ((a : A) → sample da a ≡ sample db a)
                 → da ≡D db

  sample-invariant : ∀ {A} {{_ : Eq A}} {D₁ D₂ : F A} → D₁ ≡D D₂ → (a : A) → sample D₁ a ≡ sample D₂ a
  sample-invariant (sample-equiv f) a = f a

  sample-invariant-at : ∀{A}{{_ : Eq A}}{D₁ D₂ : F A} → (a : A) → D₁ ≡D D₂ → sample D₁ a ≡ sample D₂ a
  sample-invariant-at = flip sample-invariant

  sample-diff : ∀{A}{{EQA : Eq A}} → F A → F A → A → probability
  sample-diff D₁ D₂ a = abs (sample D₁ a - sample D₂ a)

  dist-diff : ∀{A}{{_ : FiniteSet A}} → F A → F A → probability
  dist-diff {A} D₁ D₂ = sum (map (sample-diff D₁ D₂) ListEnumeration)
    where open UniqueListable {{...}}
          open Listable super-Enumeration

  bounded-dist-diff : ∀{A}{{_ : FiniteSet A}} → F A → F A → probability → Set
  bounded-dist-diff D₁ D₂ ε = dist-diff D₁ D₂ ≤ ε

  ≡D-refl : ∀{A}{{_ : Eq A}}(D : F A) → D ≡D D
  ≡D-refl D = sample-equiv λ a → refl
