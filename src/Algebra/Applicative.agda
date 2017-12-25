module Algebra.Applicative where

open import ThesisPrelude
open import Algebra.Functor

record ApplicativeProps {l l'} (F : Set l → Set l') {{AP : Applicative F}} : Set (lsuc l ⊔ l') where
  field
    <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
                    → (u <*> (v <*> w)) ≡ (pure _∘′_ <*> u <*> v <*> w)
    <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → Applicative.pure AP (f x) ≡ (pure f <*> pure x)
    <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
    overlap {{super}} : FunctorProps F
    fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)
  <*>-identity : ∀{A} (v : F A) → v ≡ (pure id <*> v)
  <*>-identity v rewrite sym (fmap-is-pure-<*> id v) = fmap-id v

open ApplicativeProps {{...}} public

ap-composition : ∀ {F : Set → Set} {{AF : Applicative F}}
                   {G : Set → Set} {{AG : Applicative G}}
                   {A B : Set}
               → F (G (A → B)) → F (G A) → F (G B)
ap-composition u v = fmap (_<*>_) u <*> v

applicative-composition : ∀ (F : Set → Set) {{AF : Applicative F}}
                            (G : Set → Set) {{AG : Applicative G}}
                        → Applicative (F ∘′ G)
applicative-composition F {{AF}} G {{AG}} = record { pure = pure ∘′ pure ; _<*>_ = ap-composition ; super = functor-composition F G }

<*>-composition-composition : ∀ (F : Set → Set) {{AF : Applicative F}} {{APF : ApplicativeProps F}}
                                (G : Set → Set) {{AG : Applicative G}} {{APG : ApplicativeProps G}}
                                {A B C} (u : F (G (B → C))) (v : F (G (A → B))) (w : F (G A))
                            → ap-composition u (ap-composition v w) ≡ ap-composition (ap-composition (ap-composition (pure (pure _∘′_)) u) v) w
<*>-composition-composition F {{AF}} {{APF}} G {{AG}} {{AGF}} u v w =
  fmap-F ap-G u <*> (fmap-F ap-G v <*> w) 
    ≡⟨ {!!} ⟩
  fmap-F ap-G (fmap-F ap-G (fmap-F (ap-G (pure-G _∘′_)) u) <*> v) <*> w
    ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G e <*> v) <*> w) (fmap-is-pure-<*> (ap-G (pure-G _∘′_)) u) ⟩
  fmap-F ap-G (fmap-F ap-G (pure-F (ap-G (pure-G _∘′_)) <*> u) <*> v) <*> w
    ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*> u ) <*> v) <*> w ) (<*>-homomorphism ap-G (pure-G _∘′_)) ⟩
  fmap-F ap-G (fmap-F ap-G (pure-F ap-G <*> pure-F (pure-G _∘′_) <*> u) <*> v) <*> w
    ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*> u) <*> v) <*> w) (fmap-is-pure-<*> ap-G (pure-F (pure-G _∘′_))) ⟩ʳ
  fmap-F ap-G (fmap-F ap-G (fmap-F ap-G (pure-F (pure-G _∘′_)) <*> u) <*> v) <*> w
  ∎
  where fmap-F : ∀{A B} → (A → B) → F A → F B
        fmap-F = fmap {{super AF}}
        pure-F : ∀{A} → A → F A
        pure-F = pure {{AF}}
        pure-G : ∀{A} → A → G A
        pure-G = pure {{AG}}
        ap-F : ∀{A B} → F (A → B) → F A → F B
        ap-F = _<*>_ {{AF}}
        ap-G : ∀{A B} → G (A → B) → G A → G B
        ap-G = _<*>_ {{AG}}

{-
<*>-homomorphism-composition : ∀{A B} (f : A → B) (x : A) → pure (f x) ≡ (pure f <*> pure x)
<*>-homomorphism-composition = ?
<*>-interchange-composition : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
<*>-interchange-composition = ? 
fmap-is-pure-<*>-composition : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)
fmap-is-pure-<*>-composition = ?

-}
