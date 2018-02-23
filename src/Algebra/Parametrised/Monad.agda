module Algebra.Parametrised.Monad where

open import ThesisPrelude

record ParMonad {l l′}(𝑺 : Set l)(M : 𝑺 → 𝑺 → Set l′ → Set l′) : Set (lsuc l′ ⊔ l) where
  infixl 1 _>>=ᵖ_
  field
    returnᵖ : ∀{S X} → X → M S S X
    _>>=ᵖ_ : ∀{S S′ S′′ X Y} → M S S′ X → (X → M S′ S′′ Y) → M S S′′ Y
    overlap {{super-functor}} : ∀{S S′} → Functor (M S S′)

open ParMonad {{...}} public

triviallyPar : ∀{l l′}(S : Set l)(M : Set l′ → Set l′){{_ : Monad M}} → ParMonad S (λ _ _ → M)
triviallyPar S M = record { returnᵖ = return ; _>>=ᵖ_ = _>>=_ }
