module Algebra.Monad where

open import ThesisPrelude
open import Algebra.Applicative

record MonadProp {l} (M : Set l → Set l) {{_ : Monad M}} : Set (lsuc l) where
  field
    >>=-assoc : ∀{X Y Z : Set l}
              → (x : M X) → (f : X → M Y) → (g : Y → M Z)
              → (x >>= f >>= g) ≡ (x >>= (λ y → f y >>= g))
    return->>=-right-id : ∀{X : Set l} → (x : M X) → x ≡ (x >>= return)
    return->>=-left-id  : ∀{X Y : Set l} → (x : X) → (f : X → M Y)
                        → (return x >>= f) ≡ f x
    overlap {{super}} : ApplicativeProp M

open MonadProp {{...}} public
