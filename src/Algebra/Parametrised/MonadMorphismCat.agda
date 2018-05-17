module Algebra.Parametrised.MonadMorphismCat where

open import ThesisPrelude
open import Algebra.Parametrised.MonadMorphism
open ParMonadMorphism

module _ {l l′}{𝑺 : Set l′}{M : 𝑺 → 𝑺 → Set l → Set l} where
  id-ParM : ParMonadMorphism M M
  StateM id-ParM = id
  TermM  id-ParM = id

module _ {l l₁′ l₂′ l₃′}
         {𝑺₁ : Set l₁′}{M₁ : 𝑺₁ → 𝑺₁ → Set l → Set l}
         {𝑺₂ : Set l₂′}{M₂ : 𝑺₂ → 𝑺₂ → Set l → Set l}
         {𝑺₃ : Set l₃′}{M₃ : 𝑺₃ → 𝑺₃ → Set l → Set l} where
  comp-ParM : ParMonadMorphism M₁ M₂ → ParMonadMorphism M₂ M₃ → ParMonadMorphism M₁ M₃
  StateM (comp-ParM m₁ m₂) = StateM m₂ ∘′ StateM m₁
  TermM  (comp-ParM m₁ m₂) = TermM m₂ ∘′ TermM m₁
