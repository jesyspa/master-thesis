import ThesisPrelude using (Applicative)
module Algebra.ApplicativeComposition {l l′ l′′} (F : Set l′ → Set l′′) {{AF : ThesisPrelude.Applicative F}}
                                                 (G : Set l  → Set l′)  {{AG : ThesisPrelude.Applicative G}} where

open import ThesisPrelude
open import Algebra.ApplicativeHelpers
open import Algebra.ApplicativeProps F renaming (ApplicativeProps to FAProps)
open import Algebra.ApplicativeProps G renaming (ApplicativeProps to GAProps; pure-F to pure-G; _<*F>_ to _<*G>_)
open import Algebra.FunctorProps F renaming (FunctorProps to FFProps)
open import Algebra.FunctorProps G renaming (FunctorProps to GFProps; fmap-F to fmap-G)
import Algebra.FunctorComposition F G as FComp
open FComp using () renaming (functor-composition to FFG)
open import Algebra.FunctorProps (F ∘′ G) renaming (FunctorProps to FFGProps; fmap-F to fmap-FG)

ap-F : ∀{A B} → F (A → B) → F A → F B
ap-F = _<*F>_
ap-G : ∀{A B} → G (A → B) → G A → G B
ap-G = _<*G>_

ap-FG : ∀ {A B : Set l} → F (G (A → B)) → F (G A) → F (G B)
ap-FG u v = fmap-F ap-G u <*F> v

instance
  applicative-composition : Applicative (F ∘′ G)
  applicative-composition = record { pure = pure-F ∘′ pure-G ; _<*>_ = ap-FG ; super = FFG }

module Props (APF : FAProps) (APG : GAProps) where
  open FFProps
  open GFProps
  open FAProps
  open GAProps
  open FComp.Props renaming (functor-props-composition to FPFG)
  open import Algebra.ApplicativeProps (F ∘′ G)
    renaming (ApplicativeProps to FGAProps; pure-F to pure-FG; _<*F>_ to _<*FG>_)

  <*>-composition-composition : ∀ {A B C} (u : F (G (B → C))) (v : F (G (A → B))) (w : F (G A))
                              → ap-FG u (ap-FG v w) ≡ ap-FG (ap-FG (ap-FG (pure-F (pure-G _∘′_)) u) v) w
  <*>-composition-composition u v w =
    fmap-F ap-G u <*F> (fmap-F ap-G v <*F> w) 
      ≡⟨ <*>-composition APF (fmap-F ap-G u) (fmap-F ap-G v) w ⟩
    pure-F (_∘′_) <*F> fmap-F ap-G u <*F> fmap-F ap-G v <*F> w
      ≡⟨ cong (λ e → e <*F> fmap-F ap-G v <*F> w)
              (fmap-is-pure-<*> APF _∘′_ (fmap-F ap-G u)) ⟩ʳ
    fmap-F (_∘′_) (fmap-F ap-G u) <*F> fmap-F ap-G v <*F> w
      ≡⟨ cong (λ e → e <*F> fmap-F ap-G v <*F> w)
              (fmap-comp (fprops APF) _∘′_ ap-G u) ⟩ʳ
    fmap-F (_∘′_ ∘′ ap-G) u <*F> fmap-F ap-G v <*F> w
      ≡⟨ cong (λ e → e <*F> w) (FAProps.ap-pairing APF (_∘′_ ∘′ ap-G) ap-G u v) ⟩
    fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure-F _,_ <*F> u <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure-F _,_ <*F> u <*F> v) <*F> e) (fmap-id (fprops APF) w) ⟩
    fmap-F (pairing-comb (_∘′_ ∘′ ap-G) ap-G) (pure-F _,_ <*F> u <*F> v) <*F> fmap id w
      ≡⟨ FAProps.ap-pairing APF (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id (pure-F _,_ <*F> u <*F> v) w ⟩
    fmap-F (pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id) (pure-F _,_ <*F> (pure-F _,_ <*F> u <*F> v) <*F> w)
      ≡⟨ fmap-ext (fprops APF)
                  (pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id)
                  (pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id)
                  G-comp-eq (pure-F _,_ <*F> (pure-F _,_ <*F> u <*F> v) <*F> w) ⟩
    fmap-F (pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id) (pure-F _,_ <*F> (pure-F _,_ <*F> u <*F> v) <*F> w)
      ≡⟨ FAProps.ap-pairing APF (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id (pure-F _,_ <*F> u <*F> v) w ⟩ʳ
    fmap-F (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure-F _,_ <*F> u <*F> v) <*F> fmap id w
      ≡⟨ cong (λ e → e <*F> fmap id w)
              (fmap-comp (fprops APF) ap-G (pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure-F _,_ <*F> u <*F> v)) ⟩
    fmap-F ap-G (fmap-F (pairing-comb (ap-G ∘′ fmap-G _∘′_) id) (pure-F _,_ <*F> u <*F> v)) <*F> fmap id w
      ≡⟨ cong (λ e → fmap-F ap-G e <*F> fmap id w)
              (FAProps.ap-pairing APF (ap-G ∘′ fmap-G _∘′_) id u v) ⟩ʳ
    fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*F> fmap id v) <*F> fmap id w
      ≡⟨ cong₂ (λ e f → fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*F> e) <*F> f)
               (fmap-id (fprops APF) v) (fmap-id (fprops APF) w) ⟩ʳ
    fmap-F ap-G (fmap-F (ap-G ∘′ fmap-G _∘′_) u <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F ap-G (e <*F> v) <*F> w)
              (fmap-comp (fprops APF) ap-G (fmap-G _∘′_) u) ⟩
    fmap-F ap-G (fmap-F ap-G (fmap-F (fmap-G _∘′_) u) <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G e <*F> v) <*F> w)
              (fmap-ext (fprops APF) (fmap-G _∘′_) (ap-G (pure-G _∘′_)) (fmap-is-pure-<*> APG _∘′_) u) ⟩
    fmap-F ap-G (fmap-F ap-G (fmap-F (ap-G (pure-G _∘′_)) u) <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G e <*F> v) <*F> w)
              (fmap-is-pure-<*> APF (ap-G (pure-G _∘′_)) u) ⟩
    fmap-F ap-G (fmap-F ap-G (pure-F (ap-G (pure-G _∘′_)) <*F> u) <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*F> u) <*F> v) <*F> w )
              (<*>-homomorphism APF ap-G (pure-G _∘′_)) ⟩
    fmap-F ap-G (fmap-F ap-G (pure-F ap-G <*F> pure-F (pure-G _∘′_) <*F> u) <*F> v) <*F> w
      ≡⟨ cong (λ e → fmap-F ap-G (fmap-F ap-G (e <*F> u) <*F> v) <*F> w)
              (fmap-is-pure-<*> APF ap-G (pure-F (pure-G _∘′_))) ⟩ʳ
    fmap-F ap-G (fmap-F ap-G (fmap-F ap-G (pure-F (pure-G _∘′_)) <*F> u) <*F> v) <*F> w
    ∎
    where G-comp-eq : ∀{A B C} → (x : (G (B → C) × G (A → B)) × G A)
                    → pairing-comb (pairing-comb (_∘′_ ∘′ ap-G) ap-G) id x ≡ pairing-comb (ap-G ∘′ pairing-comb (ap-G ∘′ fmap-G _∘′_) id) id x
          G-comp-eq ((f , g) , a) =
            ap-G f (ap-G g a)
              ≡⟨ <*>-composition APG f g a ⟩
            ap-G (ap-G (ap-G (pure-G _∘′_) f) g) a
              ≡⟨ cong (λ e → ap-G (ap-G e g) a) (fmap-is-pure-<*>  APG _∘′_ f) ⟩ʳ
            ap-G (ap-G (fmap-G _∘′_ f) g) a
            ∎
  <*>-homomorphism-composition : ∀ {A B} (f : A → B) (x : A)
                               → pure-FG (f x) ≡ ap-FG (pure-FG f) (pure-FG x)
  <*>-homomorphism-composition f x =
    pure-FG (f x)
      ≡⟨ cong pure-F (<*>-homomorphism APG f x) ⟩
    pure-F (ap-G (pure-G f) (pure-G x))
      ≡⟨ <*>-homomorphism APF (ap-G (pure-G f)) (pure-G x) ⟩
    pure-F (ap-G (pure-G f)) <*F> pure-FG x
      ≡⟨ cong (λ e → e <*F> pure-FG x) (FAProps.fmap-of-pure APF ap-G (pure-G f)) ⟩
    fmap-F ap-G (pure-F (pure-G f)) <*F> pure-FG x
    ∎

  <*>-interchange-composition : ∀{A B} (u : F (G (A → B))) (x : A) → ap-FG u (pure-FG x) ≡ ap-FG (pure-FG (λ f → f x)) u
  <*>-interchange-composition u x =
    fmap-F ap-G u <*F> pure-FG x 
      ≡⟨ <*>-interchange APF (fmap-F ap-G u) (pure-G x) ⟩
    pure-F (λ y → y (pure-G x)) <*F> fmap-F ap-G u
      ≡⟨ fmap-is-pure-<*> APF (λ y → y (pure-G x)) (fmap-F ap-G u) ⟩ʳ
    fmap-F (λ y → y (pure-G x)) (fmap-F ap-G u)
      ≡⟨ fmap-comp (fprops APF) (λ y → y (pure-G x)) ap-G u ⟩ʳ
    fmap-F (λ y → y <*G> pure-G x) u
      ≡⟨ fmap-ext (fprops APF) (λ y → y <*G> pure-G x) (ap-G (pure-G (λ f → f x))) (λ a → <*>-interchange APG a x) u ⟩
    fmap-F (ap-G (pure-G λ f → f x)) u 
      ≡⟨ fmap-is-pure-<*> APF (ap-G (pure-G (λ f → f x))) u ⟩
    pure-F (ap-G (pure-G λ f → f x)) <*F> u 
      ≡⟨ cong (λ e → e <*F> u) (FAProps.fmap-of-pure APF ap-G (pure-G (λ f → f x))) ⟩
    fmap-F ap-G (pure-FG (λ f → f x)) <*F> u
    ∎

  fmap-is-pure-<*>-composition : ∀{A B} (f : A → B) (v : F (G A)) → fmap-FG f v ≡ ap-FG (pure-FG f) v
  fmap-is-pure-<*>-composition f v =
    fmap-F (fmap-G f) v
      ≡⟨ fmap-ext (fprops APF) (fmap-G f) (ap-G (pure-G f)) (fmap-is-pure-<*> APG f) v ⟩
    fmap-F (ap-G (pure-G f)) v
      ≡⟨ fmap-is-pure-<*> APF (ap-G (pure-G f)) v ⟩
    pure-F (ap-G (pure-G f)) <*F> v
      ≡⟨ cong (λ e → e <*F> v) (FAProps.fmap-of-pure APF ap-G (pure-G f)) ⟩
    fmap-F ap-G (pure-FG f) <*F> v
    ∎
  
  applicative-props-composition : FGAProps 
  applicative-props-composition = record { <*>-composition = <*>-composition-composition 
                                         ; <*>-homomorphism = <*>-homomorphism-composition
                                         ; <*>-interchange = <*>-interchange-composition
                                         ; fprops = FPFG
                                         ; fmap-is-pure-<*>  = fmap-is-pure-<*>-composition
                                         }

