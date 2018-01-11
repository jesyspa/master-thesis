import ThesisPrelude using (Functor)
module Algebra.FunctorComposition {l l′ l′′} (F : Set l′  → Set l′′) {{FF : ThesisPrelude.Functor F}}
                                             (G : Set l → Set l′)    {{FG : ThesisPrelude.Functor G}} where

open import ThesisPrelude
open import Algebra.FunctorProps F renaming (FunctorProps to FProps)
open import Algebra.FunctorProps G renaming (FunctorProps to GProps; fmap-F to fmap-G)

instance
  functor-composition : Functor (F ∘′ G)
  functor-composition = record { fmap = fmap-F ∘′ fmap-G }

open import Algebra.FunctorProps (F ∘′ G) renaming (FunctorProps to FGProps; fmap-F to fmap-FG)

module Props {{FPF : FProps}} {{FPG : GProps}} where
  open FProps
  open GProps
  open FGProps

  fmap-ext-composition : ∀ {A B : Set l}
                       → (f g : A → B)
                       → (∀ a → f a ≡ g a)
                       → (x : F (G A))
                       → fmap-FG f x ≡ fmap-FG g x
  fmap-ext-composition f g p = fmap-ext FPF (fmap-G f) (fmap-G g) (fmap-ext FPG f g p)

  fmap-id-composition : ∀ {A : Set l}
                      → (x : F (G A))
                      → x ≡ fmap-FG id x
  fmap-id-composition = FProps.fmap-ext-id FPF (fmap-G id) (fmap-id FPG)
  
  fmap-comp-composition : ∀ {A B C : Set l}
                               → (g : B → C) → (f : A → B) → (x : F (G A))
                               → fmap-FG (g ∘′ f) x
                                   ≡
                                 fmap-FG g (fmap-FG f x)
  fmap-comp-composition g f x =
    fmap-FG  (g ∘′ f) x
      ≡⟨ refl ⟩
    fmap-F (fmap-G (g ∘′ f)) x
      ≡⟨ fmap-ext FPF (fmap-G (g ∘′ f)) (fmap-G g ∘′ fmap-G f) (fmap-comp FPG g f) x ⟩
    fmap-F (fmap-G g ∘′ fmap-G f) x
      ≡⟨ fmap-comp FPF (fmap-G g) (fmap-G f) x ⟩
    fmap-FG g (fmap-FG f x)
    ∎
  
  instance
    functor-props-composition : FGProps
    functor-props-composition = record { fmap-ext = fmap-ext-composition
                                       ; fmap-id = fmap-id-composition
                                       ; fmap-comp = fmap-comp-composition
                                       }
