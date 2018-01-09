import ThesisPrelude using (Applicative)
module Algebra.ApplicativeProps {l l′} (F : Set l → Set l′) (AF : ThesisPrelude.Applicative F) where

open import ThesisPrelude
open import Algebra.ApplicativeHelpers
open import Algebra.FunctorProps F (super AF) renaming (FunctorProps to FProps)
open FProps

pure-F : ∀{A : Set l} → A → F A
pure-F = pure {{AF}}
infixl 4 _<*F>_
_<*F>_ : ∀{A B : Set l} → F (A → B) → F A → F B
_<*F>_ = _<*>_ {{AF}}

record ApplicativeProps : Set (lsuc l ⊔ l′) where
  field
    <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
                    → (u <*F> (v <*F> w)) ≡ (pure-F _∘′_ <*F> u <*F> v <*F> w)
    <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → pure-F (f x) ≡ (pure-F f <*F> pure-F x)
    <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*F> pure-F x) ≡ (pure-F (λ f → f x) <*F> u)
    fprops : FProps 
    fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure-F f <*F> v)
  <*>-identity : ∀{A} (v : F A) → v ≡ (pure-F id <*F> v)
  <*>-identity v rewrite sym (fmap-is-pure-<*> id v) = fmap-id fprops v
  fmap-of-pure : ∀{A B} (f : A → B) (v : A) → pure-F (f v) ≡ fmap f (pure-F v)
  fmap-of-pure f v = <*>-homomorphism f v ⟨≡⟩ʳ fmap-is-pure-<*> f (pure-F v)
  ap-pairing : ∀{A B C D} (f : A → C → D) (g : B → C) (u : F A) (v : F B)
             → (fmap f u <*F> fmap g v) ≡ fmap-F (pairing-comb f g) (pure-F _,_ <*F> u <*F> v)
  ap-pairing f g u v =
    fmap-F f u <*F> fmap-F g v
      ≡⟨ cong (λ e → fmap-F f u <*F> e) (fmap-is-pure-<*> g v) ⟩
    fmap-F f u <*F> (pure-F g <*F> v)
      ≡⟨ <*>-composition (fmap-F f u) (pure-F g) v ⟩
    pure-F (_∘′_) <*F> fmap-F f u <*F> pure-F g <*F> v
      ≡⟨ cong (λ e → e <*F> pure-F g <*F> v) (fmap-is-pure-<*> _∘′_ (fmap-F f u)) ⟩ʳ
    fmap-F (_∘′_) (fmap-F f u) <*F> pure-F g <*F> v
      ≡⟨ cong (λ e → e <*F> v) (<*>-interchange (fmap-F (_∘′_) (fmap-F f u)) g) ⟩
    pure-F (λ y → y g) <*F> fmap-F (_∘′_) (fmap-F f u) <*F> v
      ≡⟨ cong (λ e → pure-F (λ y → y g) <*F> e <*F> v) (fmap-comp fprops _∘′_ f u) ⟩ʳ
    pure-F (λ y → y g) <*F> fmap-F (_∘′_ ∘′ f) u <*F> v
      ≡⟨ cong (λ e → e <*F> v) (fmap-is-pure-<*> (λ y → y g) (fmap-F (_∘′_ ∘′ f) u)) ⟩ʳ
    fmap-F (λ y → y g) (fmap-F (_∘′_ ∘′ f) u) <*F> v
      ≡⟨ cong (λ e → e <*F> v) (fmap-comp fprops (λ z → z g) (_∘′_ ∘′ f) u) ⟩ʳ
    fmap-F (λ a b → pairing-comb f g (a , b)) u <*F> v
      ≡⟨ cong (λ e → e <*F> v) (fmap-comp fprops (_∘′_ (pairing-comb f g)) _,_ u) ⟩
    fmap-F (_∘′_ (pairing-comb f g)) (fmap-F _,_ u) <*F> v
      ≡⟨ cong (λ e → fmap-F (_∘′_ (pairing-comb f g)) e <*F> v) (fmap-is-pure-<*> _,_ u) ⟩
    fmap-F (_∘′_ (pairing-comb f g)) (pure-F _,_ <*F> u) <*F> v
      ≡⟨ cong (λ e → e <*F> v) (fmap-is-pure-<*> (_∘′_ (pairing-comb f g)) (pure-F _,_ <*F> u)) ⟩
    pure-F (_∘′_ (pairing-comb f g)) <*F> (pure-F _,_ <*F> u) <*F> v
      ≡⟨ cong (λ e → e <*F> (pure-F _,_ <*F> u) <*F> v) (<*>-homomorphism _∘′_ (pairing-comb f g)) ⟩
    pure-F (_∘′_) <*F> pure-F (pairing-comb f g) <*F> (pure-F _,_ <*F> u) <*F> v
      ≡⟨ <*>-composition (pure-F (pairing-comb f g)) (pure-F _,_ <*F> u) v ⟩ʳ
    pure-F (pairing-comb f g) <*F> (pure-F _,_ <*F> u <*F> v)
      ≡⟨ fmap-is-pure-<*> (pairing-comb f g) (pure-F _,_ <*F> u <*F> v) ⟩ʳ
    fmap-F (pairing-comb f g) (pure-F _,_ <*F> u <*F> v)
    ∎
