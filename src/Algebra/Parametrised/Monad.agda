module Algebra.Parametrised.Monad where

open import ThesisPrelude

record ParMonad {l}(𝑺 : Set l)(M : 𝑺 → 𝑺 → Set l → Set l) : Set (lsuc l) where
  infixl 1 _>>=ᵖ_
  field
    returnᵖ : ∀{S X} → X → M S S X
    _>>=ᵖ_ : ∀{S S′ S′′ X Y} → M S S′ X → (X → M S′ S′′ Y) → M S S′′ Y
    overlap {{super-functor}} : ∀{S S′} → Functor (M S S′)




