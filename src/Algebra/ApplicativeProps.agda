import ThesisPrelude using (Applicative)
module Algebra.ApplicativeProps {l l′} (F : Set l → Set l′) {{AF : ThesisPrelude.Applicative F}} where

open import ThesisPrelude
open import Algebra.ApplicativeHelpers
open import Algebra.FunctorProps F renaming (FunctorProps to FProps)
open FProps {{...}}

pure-F : ∀{A : Set l} → A → F A
pure-F = pure {{AF}}
infixl 4 _<*F>_
_<*F>_ : ∀{A B : Set l} → F (A → B) → F A → F B
_<*F>_ = _<*>_ {{AF}}

record ApplicativeProps : Set (lsuc l ⊔ l′) where
  field
    <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
                    → (u <*> (v <*> w)) ≡ (pure _∘′_ <*> u <*> v <*> w)
    <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → pure (f x) ≡ (pure f <*> pure x) as F B
    <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
    overlap {{fprops}} : FProps 
    fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)
  <*>-identity : ∀{A} (v : F A) → v ≡ (pure id <*> v)
  <*>-identity v rewrite sym (fmap-is-pure-<*> id v) = fmap-id v
  fmap-of-pure : ∀{A B} (f : A → B) (v : A) → pure (f v) ≡ fmap f (pure v)
  fmap-of-pure f v = <*>-homomorphism f v ⟨≡⟩ʳ fmap-is-pure-<*> f (pure v)
  ap-pairing : ∀{A B C D} (f : A → C → D) (g : B → C) (u : F A) (v : F B)
             → (fmap f u <*> fmap g v) ≡ fmap (pairing-comb f g) (pure _,_ <*> u <*> v)
  ap-pairing f g u v =
    fmap f u <*> fmap g v
      ≡⟨ cong (λ e → fmap f u <*> e) (fmap-is-pure-<*> g v) ⟩
    fmap f u <*> (pure g <*> v)
      ≡⟨ <*>-composition (fmap f u) (pure g) v ⟩
    pure (_∘′_) <*> fmap f u <*> pure g <*> v
      ≡⟨ cong (λ e → e <*> pure g <*> v) (fmap-is-pure-<*> _∘′_ (fmap f u)) ⟩ʳ
    fmap (_∘′_) (fmap f u) <*> pure g <*> v
      ≡⟨ cong (λ e → e <*> v) (<*>-interchange (fmap (_∘′_) (fmap f u)) g) ⟩
    pure (λ y → y g) <*> fmap (_∘′_) (fmap f u) <*> v
      ≡⟨ cong (λ e → pure (λ y → y g) <*> e <*> v) (fmap-comp _∘′_ f u) ⟩ʳ
    pure (λ y → y g) <*> fmap (_∘′_ ∘′ f) u <*> v
      ≡⟨ cong (λ e → e <*> v) (fmap-is-pure-<*> (λ y → y g) (fmap (_∘′_ ∘′ f) u)) ⟩ʳ
    fmap (λ y → y g) (fmap (_∘′_ ∘′ f) u) <*> v
      ≡⟨ cong (λ e → e <*> v) (fmap-comp (λ z → z g) (_∘′_ ∘′ f) u) ⟩ʳ
    fmap (λ a b → pairing-comb f g (a , b)) u <*> v
      ≡⟨ cong (λ e → e <*> v) (fmap-comp (_∘′_ (pairing-comb f g)) _,_ u) ⟩
    fmap (_∘′_ (pairing-comb f g)) (fmap _,_ u) <*> v
      ≡⟨ cong (λ e → fmap (_∘′_ (pairing-comb f g)) e <*> v) (fmap-is-pure-<*> _,_ u) ⟩
    fmap (_∘′_ (pairing-comb f g)) (pure _,_ <*> u) <*> v
      ≡⟨ cong (λ e → e <*> v) (fmap-is-pure-<*> (_∘′_ (pairing-comb f g)) (pure _,_ <*> u)) ⟩
    pure (_∘′_ (pairing-comb f g)) <*> (pure _,_ <*> u) <*> v
      ≡⟨ cong (λ e → e <*> (pure _,_ <*> u) <*> v) (<*>-homomorphism _∘′_ (pairing-comb f g)) ⟩
    pure (_∘′_) <*> pure (pairing-comb f g) <*> (pure _,_ <*> u) <*> v
      ≡⟨ <*>-composition (pure (pairing-comb f g)) (pure _,_ <*> u) v ⟩ʳ
    pure (pairing-comb f g) <*> (pure _,_ <*> u <*> v)
      ≡⟨ fmap-is-pure-<*> (pairing-comb f g) (pure _,_ <*> u <*> v) ⟩ʳ
    fmap (pairing-comb f g) (pure _,_ <*> u <*> v)
    ∎
