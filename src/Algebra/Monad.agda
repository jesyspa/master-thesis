module Algebra.Monad where

open import ThesisPrelude
open import Algebra.Applicative

record MonadProps {l} (M : Set l → Set l) {{_ : Monad M}} : Set (lsuc l) where
  field
    >>=-assoc : ∀{A B C}
              → (x : M A) → (f : A → M B) → (g : B → M C)
              → (x >>= f >>= g) ≡ (x >>= (λ y → f y >>= g))
    return->>=-right-id : ∀{A} → (x : M A) → x ≡ (x >>= return)
    return->>=-left-id  : ∀{A B} → (x : A) → (f : A → M B)
                        → (return x >>= f) ≡ f x
    overlap {{super}} : ApplicativeProps M
    <*>-is-ap : ∀{A B} (v : M (A → B)) (w : M A)
              → (v <*> w) ≡ (v >>= λ f → w >>= λ x → return (f x))

  return-simplify : ∀{A B} → (f : A → B) → (v : M A)
                  → fmap f v ≡ (v >>= λ x → return (f x))
  return-simplify f v =
    fmap f v
      ≡⟨ fmap-is-pure-<*> f v ⟩
    pure f <*> v
      ≡⟨ <*>-is-ap (pure f) v ⟩
    pure f >>= (λ g → v >>= λ x → pure (g x))
      ≡⟨ return->>=-left-id f (λ g → v >>= λ x → pure (g x)) ⟩
    (λ g → v >>= λ x → pure (g x)) f 
      ≡⟨ refl ⟩
    v >>= (λ x → pure (f x))
    ∎

open MonadProps {{...}} public
