module Algebra.Monad where

open import ThesisPrelude
open import Algebra.Applicative

record MonadProp {l} (M : Set l → Set l) {{_ : Monad M}} : Set (lsuc l) where
  field
    >>=-assoc : ∀{X Y Z}
              → (x : M X) → (f : X → M Y) → (g : Y → M Z)
              → (x >>= f >>= g) ≡ (x >>= (λ y → f y >>= g))
    return->>=-right-id : ∀{X} → (x : M X) → x ≡ (x >>= return)
    return->>=-left-id  : ∀{X Y} → (x : X) → (f : X → M Y)
                        → (return x >>= f) ≡ f x
    overlap {{super}} : ApplicativeProps M
    <*>-is-ap : ∀{X Y} (v : M (X → Y)) (w : M X)
              → (v <*> w) ≡ (v >>= λ f → w >>= λ x → return (f x))

  return-simplify : ∀{X Y} → (v : M X) → (f : X → Y)
                  → fmap f v ≡ (v >>= λ x → return (f x))
  return-simplify v f =
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

open MonadProp {{...}} public
