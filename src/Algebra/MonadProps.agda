import ThesisPrelude using (Monad)
module Algebra.MonadProps {l} (F : Set l → Set l) (MF : ThesisPrelude.Monad F) where

open import ThesisPrelude
open import Algebra.Applicative

infixl 1 _>>F=_
_>>F=_ : ∀{A B} → F A → (A → F B) → F B
_>>F=_ = _>>=_ {{MF}}

return-F : ∀{A} → A → F A
return-F = return {{MF}}

record MonadProps : Set (lsuc l) where
  field
    >>=-assoc : ∀{A B C}
              → (x : F A) → (f : A → F B) → (g : B → F C)
              → (x >>F= f >>F= g) ≡ (x >>F= (λ y → f y >>F= g))
    return->>=-right-id : ∀{A} → (x : F A) → x ≡ (x >>F= return-F)
    return->>=-left-id  : ∀{A B} → (x : A) → (f : A → F B)
                        → (return-F x >>F= f) ≡ f x
    overlap {{super}} : ApplicativeProps F
    <*>-is-ap : ∀{A B} (v : F (A → B)) (w : F A)
              → (v <*> w) ≡ (v >>F= λ f → w >>F= λ x → return-F (f x))

  return-simplify : ∀{A B} → (f : A → B) → (v : F A)
                  → fmap f v ≡ (v >>F= λ x → return-F (f x))
  return-simplify f v =
    fmap f v
      ≡⟨ fmap-is-pure-<*> f v ⟩
    pure f <*> v
      ≡⟨ <*>-is-ap (pure f) v ⟩
    pure f >>F= (λ g → v >>F= λ x → pure (g x))
      ≡⟨ return->>=-left-id f (λ g → v >>F= λ x → pure (g x)) ⟩
    (λ g → v >>F= λ x → pure (g x)) f 
      ≡⟨ refl ⟩
    v >>F= (λ x → pure (f x))
    ∎

open MonadProps {{...}} public
