module Algebra.Applicative where

open import ThesisPrelude
open import Algebra.Functor

pairing-comb : ∀{l} {A B C D : Set l} (f : A → C → D) (g : B → C) → A × B → D
pairing-comb f g (a , b) = f a (g b)

record ApplicativeProps {l l'} (F : Set l → Set l') {{AP : Applicative F}} : Set (lsuc l ⊔ l') where
  pure-AP : ∀{A : Set l} → A → F A
  pure-AP = pure
  fmap-AP : ∀{A B : Set l} → (A → B) → F A → F B
  fmap-AP = fmap
  field
    <*>-composition : ∀{A B C} (u : F (B → C)) (v : F (A → B)) (w : F A)
                    → (u <*> (v <*> w)) ≡ (pure _∘′_ <*> u <*> v <*> w)
    <*>-homomorphism : ∀{A B} (f : A → B) (x : A) → pure-AP (f x) ≡ (pure f <*> pure x)
    <*>-interchange : ∀{A B} (u : F (A → B)) (x : A) → (u <*> pure x) ≡ (pure (λ f → f x) <*> u)
    overlap {{super}} : FunctorProps F
    fmap-is-pure-<*> : ∀{A B} (f : A → B) (v : F A) → fmap f v ≡ (pure f <*> v)
  <*>-identity : ∀{A} (v : F A) → v ≡ (pure id <*> v)
  <*>-identity v rewrite sym (fmap-is-pure-<*> id v) = fmap-id v
  fmap-of-pure : ∀{A B} (f : A → B) (v : A) → pure-AP (f v) ≡ fmap f (pure-AP v)
  fmap-of-pure f v = <*>-homomorphism f v ⟨≡⟩ʳ fmap-is-pure-<*> f (pure v)
  ap-pairing : ∀{A B C D} (f : A → C → D) (g : B → C) (u : F A) (v : F B)
             → (fmap f u <*> fmap g v) ≡ fmap-AP (pairing-comb f g) (pure-AP _,_ <*> u <*> v)
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
    fmap (pairing-comb f g) (pure-AP _,_ <*> u <*> v)
    ∎

open ApplicativeProps {{...}} public

module _ (F : Set → Set) {{AF : Applicative F}} (G : Set → Set) {{AG : Applicative G}} where
  fmap-F : ∀{A B} → (A → B) → F A → F B
  fmap-F = fmap
  fmap-G : ∀{A B} → (A → B) → G A → G B
  fmap-G = fmap
  pure-F : ∀{A} → A → F A
  pure-F = pure
  pure-G : ∀{A} → A → G A
  pure-G = pure
  ap-F : ∀{A B} → F (A → B) → F A → F B
  ap-F = _<*>_
  ap-G : ∀{A B} → G (A → B) → G A → G B
  ap-G = _<*>_

  fmap-FG : ∀{A B} → (A → B) → F (G A) → F (G B)
  fmap-FG f = fmap (fmap f)

  pure-FG : ∀{A} → A → F (G A)
  pure-FG = pure ∘′ pure

  ap-FG : ∀ {A B : Set} → F (G (A → B)) → F (G A) → F (G B)
  ap-FG u v = fmap-F ap-G u <*> v
  
  applicative-composition : Applicative (F ∘′ G)
  applicative-composition = record { pure = pure-FG ; _<*>_ = ap-FG ; super = functor-composition F G }
  
  module _ {{APF : ApplicativeProps F}} {{APG : ApplicativeProps G}} where
    <*>-composition-composition : ∀ {A B C} (u : F (G (B → C))) (v : F (G (A → B))) (w : F (G A))
                                → ap-FG u (ap-FG v w) ≡ ap-FG (ap-FG (ap-FG (pure-F (pure-G _∘′_)) u) v) w
    <*>-composition-composition u v w =
      fmap-F ap-G u <*> (fmap-F ap-G v <*> w) 
        ≡⟨ <*>-composition (fmap-F ap-G u) (fmap-F ap-G v) w ⟩
      pure-F (_∘′_) <*> fmap-F ap-G u <*> fmap-F ap-G v <*> w
        ≡⟨ cong (λ e → e <*> fmap-F ap-G v <*> w)
                (fmap-is-pure-<*> _∘′_ (fmap-F ap-G u)) ⟩ʳ
      fmap-F (_∘′_) (fmap-F ap-G u) <*> fmap-F ap-G v <*> w
        ≡⟨ cong (λ e → e <*> fmap-F ap-G v <*> w)
                (fmap-comp _∘′_ ap-G u) ⟩ʳ
      fmap-F (_∘′_ ∘′ ap-G) u <*> fmap-F ap-G v <*> w
        ≡⟨ cong (λ e → e <*> w) (ap-pairing (_∘′_ ∘′ ap-G) ap-G u v) ⟩
      fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure-F _,_ <*> u <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure _,_ <*> u <*> v) <*> e) (fmap-id w) ⟩
      fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure-F _,_ <*> u <*> v) <*> fmap id w
        ≡⟨ ap-pairing (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id (pure-F _,_ <*> u <*> v) w ⟩
      fmap-F (pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id) (pure-F _,_ <*> (pure-F _,_ <*> u <*> v) <*> w)
        ≡⟨ fmap-ext (pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id)
                    (pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id)
                    G-comp-eq (pure _,_ <*> (pure _,_ <*> u <*> v) <*> w) ⟩
      fmap-F (pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id) (pure _,_ <*> (pure _,_ <*> u <*> v) <*> w)
        ≡⟨ ap-pairing (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id (pure _,_ <*> u <*> v) w ⟩ʳ
      fmap-F (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure _,_ <*> u <*> v) <*> fmap id w
        ≡⟨ cong (λ e → e <*> fmap id w) (fmap-comp ap-G (pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure _,_ <*> u <*> v)) ⟩
      fmap-F ap-G (fmap-F (pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure _,_ <*> u <*> v)) <*> fmap id w
        ≡⟨ cong (λ e → fmap-F ap-G e <*> fmap id w) (ap-pairing (ap-G ∘′ fmap-G _∘′_) id u v) ⟩ʳ
      fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*> fmap id v) <*> fmap id w
        ≡⟨ cong₂ (λ e f → fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*> e) <*> f) (fmap-id v) (fmap-id w) ⟩ʳ
      fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F ap-G (e <*> v) <*> w)
                (fmap-comp ap-G (fmap-G _∘′_) u) ⟩
      fmap-F ap-G (fmap-F ap-G (fmap-F (fmap-G _∘′_) u) <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G e <*> v) <*> w)
                (fmap-ext (fmap-G _∘′_) (ap-G (pure-G _∘′_)) (fmap-is-pure-<*> _∘′_) u) ⟩
      fmap-F ap-G (fmap-F ap-G (fmap-F (ap-G (pure-G _∘′_)) u) <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G e <*> v) <*> w)
                (fmap-is-pure-<*> (ap-G (pure-G _∘′_)) u) ⟩
      fmap-F ap-G (fmap-F ap-G (pure-F (ap-G (pure-G _∘′_)) <*> u) <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*> u) <*> v) <*> w )
                (<*>-homomorphism ap-G (pure-G _∘′_)) ⟩
      fmap-F ap-G (fmap-F ap-G (pure-F ap-G <*> pure-F (pure-G _∘′_) <*> u) <*> v) <*> w
        ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*> u) <*> v) <*> w)
                (fmap-is-pure-<*> ap-G (pure-F (pure-G _∘′_))) ⟩ʳ
      fmap-F ap-G (fmap-F ap-G (fmap-F ap-G (pure-F (pure-G _∘′_)) <*> u) <*> v) <*> w
      ∎
      where G-comp-eq : ∀{A B C} → (x : (G (B → C) × G (A → B)) × G A)
                      → pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id x ≡ pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id x
            G-comp-eq ((f , g) , a) =
              ap-G f (ap-G g a)
                ≡⟨ <*>-composition f g a ⟩
              ap-G (ap-G (ap-G (pure-G _∘′_) f) g) a
                ≡⟨ cong (λ e → ap-G (ap-G e g) a) (fmap-is-pure-<*> _∘′_ f) ⟩ʳ
              ap-G (ap-G (fmap-G _∘′_ f) g) a
              ∎

    <*>-homomorphism-composition : ∀ {A B} (f : A → B) (x : A)
                                 → pure-FG (f x) ≡ ap-FG (pure-FG f) (pure-FG x)
    <*>-homomorphism-composition f x =
      pure-FG (f x)
        ≡⟨ cong pure-F (<*>-homomorphism f x) ⟩
      pure-F (ap-G (pure-G f) (pure-G x))
        ≡⟨ <*>-homomorphism (ap-G (pure-G f)) (pure-G x) ⟩
      pure-F (ap-G (pure-G f)) <*> pure-FG x
        ≡⟨ cong (λ e → e <*> pure-FG x) (fmap-of-pure ap-G (pure-G f)) ⟩
      fmap-F ap-G (pure-F (pure-G f)) <*> pure-FG x
      ∎

    <*>-interchange-composition : ∀{A B} (u : F (G (A → B))) (x : A) → ap-FG u (pure-FG x) ≡ ap-FG (pure-FG (λ f → f x)) u
    <*>-interchange-composition u x =
      fmap-F ap-G u <*> pure-FG x 
        ≡⟨ <*>-interchange (fmap ap-G u) (pure-G x) ⟩
      pure-F (λ y → y (pure-G x)) <*> fmap ap-G u
        ≡⟨  fmap-is-pure-<*> (λ y → y (pure-G x)) (fmap ap-G u) ⟩ʳ
      fmap-F (λ y → y (pure-G x)) (fmap ap-G u)
        ≡⟨ fmap-comp (λ y → y (pure-G x)) ap-G u ⟩ʳ
      fmap-F (λ y → y <*> pure-G x) u
        ≡⟨ fmap-ext (λ y → y <*> pure-G x) (ap-G (pure-G (λ f → f x))) (λ a → <*>-interchange a x) u ⟩
      fmap-F (ap-G (pure-G λ f → f x)) u 
        ≡⟨ fmap-is-pure-<*> (ap-G (pure-G (λ f → f x))) u ⟩
      pure-F (ap-G (pure-G λ f → f x)) <*> u 
        ≡⟨ cong (λ e → e <*> u) (fmap-of-pure ap-G (pure-G (λ f → f x))) ⟩
      fmap-F ap-G (pure-FG (λ f → f x)) <*> u
      ∎

    fmap-is-pure-<*>-composition : ∀{A B} (f : A → B) (v : F (G A)) → fmap-FG f v ≡ ap-FG (pure-FG f) v
    fmap-is-pure-<*>-composition f v =
      fmap (fmap f) v
        ≡⟨ fmap-ext (fmap f) (ap-G (pure-G f)) (fmap-is-pure-<*> f) v ⟩
      fmap-F (ap-G (pure-G f)) v
        ≡⟨ fmap-is-pure-<*> (ap-G (pure-G f)) v ⟩
      pure-F (ap-G (pure-G f)) <*> v
        ≡⟨ cong (λ e → e <*> v) (fmap-of-pure ap-G (pure-G f)) ⟩
      fmap-F ap-G (pure-FG f) <*> v
      ∎
    
    applicative-props-composition : ApplicativeProps (F ∘′ G) {{applicative-composition}}
    applicative-props-composition = record { <*>-composition = <*>-composition-composition 
                                           ; <*>-homomorphism = <*>-homomorphism-composition
                                           ; <*>-interchange = <*>-interchange-composition
                                           ; super = functor-props-composition F G
                                           ; fmap-is-pure-<*>  = fmap-is-pure-<*>-composition
                                           }
