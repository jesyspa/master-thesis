module Algebra.Functor where

open import ThesisPrelude
open import Algebra.Function

record FunctorProps {l l'} (F : Set l → Set l') {{FF : Functor F}} : Set (lsuc l ⊔ l') where
  field
    fmap-ext : ∀{A B} (f g : A → B)
             → (∀ a → f a ≡ g a)
             → (x : F A)
             → fmap f x ≡ fmap g x
    fmap-id : ∀{A} → (x : F A) → x ≡ fmap id x
    fmap-comp : ∀{A B C} (g : B → C) (f : A → B) (x : F A) 
              → fmap (g ∘ f) x ≡ fmap g (fmap f x)
  fmap-ext-id : ∀{A} (f : A → A)
              → (∀ a → a ≡ f a)
              → (x : F A)
              → x ≡ fmap f x
  fmap-ext-id f p x = fmap-id x ⟨≡⟩ fmap-ext id f p x
  fmap-lift-ret : ∀{A B} (g : B → A) (f : A → B)
                → Retraction g of f
                → Retraction fmap {{FF}} g of fmap f
  fmap-lift-ret g f rp x = fmap-ext-id (g ∘′ f) rp x ⟨≡⟩ fmap-comp g f x

open FunctorProps {{...}} public


functor-composition : ∀ (F : Set → Set) {{FF : Functor F}}
                        (G : Set → Set) {{FG : Functor G}}
                    → Functor (F ∘′ G)
functor-composition F {{FF}} G {{FG}} = record { fmap = fmap {{FF}} ∘′ fmap {{FG}} }

fmap-ext-composition : ∀ {A B : Set}
                       (F : Set → Set) {{FF : Functor F}} {{FPF : FunctorProps F}}
                       (G : Set → Set) {{FG : Functor G}} {{FPG : FunctorProps G}}
                     → (f g : A → B)
                     → (∀ a → f a ≡ g a)
                     → (x : F (G A))
                     → fmap {{functor-composition F G}} f x ≡ fmap {{functor-composition F G}} g x
fmap-ext-composition F G f g p = fmap-ext (fmap f) (fmap g) (fmap-ext f g p)

fmap-id-composition : ∀ {A : Set}
                      (F : Set → Set) {{FF : Functor F}} {{FPF : FunctorProps F}}
                      (G : Set → Set) {{FG : Functor G}} {{FPG : FunctorProps G}}
                    → (x : F (G A))
                    → x ≡ fmap {{functor-composition F G}} id x
fmap-id-composition F G = fmap-ext-id (fmap id) fmap-id

fmap-comp-composition : ∀ {A B C : Set}
                               (F : Set → Set) {{FF : Functor F}} {{FPF : FunctorProps F}}
                               (G : Set → Set) {{FG : Functor G}} {{FPG : FunctorProps G}}
                             → (g : B → C) → (f : A → B) → (x : F (G A))
                             → fmap {{functor-composition F G}} (g ∘′ f) x
                                 ≡
                               fmap {{functor-composition F G}} g (fmap {{functor-composition F G}} f x)
fmap-comp-composition F G g f x =
  fmap {{functor-composition F G}} (g ∘′ f) x
    ≡⟨ refl ⟩
  fmap (fmap (g ∘′ f)) x
    ≡⟨ fmap-ext (fmap (g ∘′ f)) (fmap g ∘′ fmap f) (fmap-comp g f) x ⟩
  fmap (fmap g ∘′ fmap f) x
    ≡⟨ fmap-comp (fmap g) (fmap f) x ⟩
  fmap {{functor-composition F G}} g (fmap {{functor-composition F G}} f x)
  ∎

functor-props-composition : ∀ (F : Set → Set) {{FF : Functor F}} {{FPF : FunctorProps F}}
                              (G : Set → Set) {{FG : Functor G}} {{FPG : FunctorProps G}}
                         → FunctorProps (F ∘ G) {{functor-composition F G}}
functor-props-composition F {{FF}} {{FPF}} G {{FG}} {{FPG}} = record { fmap-ext = fmap-ext-composition F G
                                                                     ; fmap-id = fmap-id-composition F G
                                                                     ; fmap-comp = fmap-comp-composition F G
                                                                     }
