open import Algebra.Parametrised.Monad using (ParMonad)
module Algebra.Parametrised.MonadProps {l l′}(𝑺 : Set l′)(M : 𝑺 → 𝑺 → Set l → Set l){{PMM : ParMonad 𝑺 M}} where

open import ThesisPrelude
open import Algebra.FunctorProps
open import Algebra.Parametrised.Monad

infixl 1 _>>M=ᵖ_
_>>M=ᵖ_ : ∀{S₀ S₁ S₂ A B} → M S₀ S₁ A → (A → M S₁ S₂ B) → M S₀ S₂ B
_>>M=ᵖ_ = ParMonad._>>=ᵖ_ PMM

record ParMonadProps : Set (lsuc l ⊔ l′) where
  field
    >>=-assocᵖ : ∀{S₀ S₁ S₂ S₃ A B C}
              → (x : M S₀ S₁ A) → (f : A → M S₁ S₂ B) → (g : B → M S₂ S₃ C)
              → (x >>=ᵖ f >>=ᵖ g) ≡ (x >>=ᵖ (λ a → f a >>=ᵖ g))
    return->>=-right-idᵖ : ∀{S S′ A} → (x : M S S′ A) → x ≡ (x >>=ᵖ returnᵖ)
    return->>=-left-idᵖ  : ∀{S S′ A B} → (x : A) → (f : A → M S S′ B)
                        → (returnᵖ x >>=ᵖ f) ≡ f x
    >>=-extᵖ : ∀{S₀ S₁ S₂ A B} (x : M S₀ S₁ A) (f g : A → M S₁ S₂ B)
            → (∀ a → f a ≡ g a)
            → (x >>=ᵖ f) ≡ (x >>=ᵖ g)
    overlap {{functor-props}} : ∀{S S′} → FunctorProps (M S S′)
