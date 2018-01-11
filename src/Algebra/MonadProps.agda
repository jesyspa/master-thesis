import ThesisPrelude using (Monad)
module Algebra.MonadProps {l} (F : Set l → Set l) {{MF : ThesisPrelude.Monad F}} where

open import ThesisPrelude
open import Algebra.ApplicativeProps F

open ApplicativeProps {{...}}

infixl 1 _>>F=_
_>>F=_ : ∀{A B} → F A → (A → F B) → F B
_>>F=_ = _>>=_

return-F : ∀{A} → A → F A
return-F = return

record MonadProps : Set (lsuc l) where
  field
    >>=-assoc : ∀{A B C}
              → (x : F A) → (f : A → F B) → (g : B → F C)
              → (x >>= f >>= g) ≡ (x >>= (λ y → f y >>= g))
    return->>=-right-id : ∀{A} → (x : F A) → x ≡ (x >>= return)
    return->>=-left-id  : ∀{A B} → (x : A) → (f : A → F B)
                        → (return x >>= f) ≡ f x
    overlap {{aprops}} : ApplicativeProps
    <*>-is-ap : ∀{A B} (v : F (A → B)) (w : F A)
              → (v <*> w) ≡ (v >>= λ f → w >>= λ x → return (f x))

  return-simplify : ∀{A B} → (f : A → B) → (v : F A)
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

