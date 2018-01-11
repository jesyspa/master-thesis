open import ThesisPrelude using (Monoid)
module Utility.Writer {l} (Q : Set l) {{QM : Monoid Q}} where

open import ThesisPrelude
open import Algebra.Monoid

Writer : Set l → Set l
Writer A = A × Q

fmap-W : ∀{A B : Set l} → (A → B) → Writer A → Writer B 
fmap-W f (a , q) = f a , q

fmap-W-ext : ∀{A B} (f g : A → B)
               → (∀ a → f a ≡ g a)
               → (x : Writer A)
               → fmap-W f x ≡ fmap-W g x
fmap-W-ext f g p (a , q) rewrite p a = refl

fmap-W-id : ∀{A}
              → (x : Writer A)
              → x ≡ fmap-W id x
fmap-W-id (a , q) = refl 

fmap-W-comp : ∀{A B C} (g : B → C) (f : A → B) (x : Writer A)
                → fmap-W (g ∘′ f) x ≡ fmap-W g (fmap-W f x)
fmap-W-comp g f (a , q) = refl

make-W : ∀{A} → Q → A → Writer A
make-W q a = a , q

instance
  FunctorWriter : Functor Writer
  FunctorWriter = record { fmap = fmap-W }

open import Algebra.FunctorProps Writer

instance
  FunctorPropsWriter : FunctorProps
  FunctorPropsWriter = record { fmap-ext = fmap-W-ext ; fmap-id = fmap-W-id ; fmap-comp = fmap-W-comp }


ap-W : ∀{A B : Set l} → Writer (A → B) → Writer A → Writer B
ap-W (f , v₁) (a , v₂) = f a , v₁ <> v₂

pure-W : ∀{A : Set l} → A → Writer A
pure-W = make-W mempty

instance
  ApplicativeWriter : Applicative Writer
  ApplicativeWriter = record { pure = pure-W ; _<*>_ = ap-W }

bind-W : ∀{A B : Set l} → Writer A → (A → Writer B) → Writer B
bind-W (x , v) f with f x
... | y , w = y , v <> w

instance
  MonadWriter : Monad Writer
  MonadWriter = record { _>>=_ = bind-W ; super = ApplicativeWriter }

open import Algebra.ApplicativeProps Writer
open import Algebra.MonadProps Writer

module Props {{QP : MonoidProps Q}} where
  ap-W-composition : ∀{A B C} (u : Writer (B → C)) (v : Writer (A → B)) (w : Writer A)
                  → ap-W u (ap-W v w) ≡ ap-W (ap-W (ap-W (pure-W _∘′_) u) v) w
  ap-W-composition (f , a) (g , b) (h , c)
    rewrite sym (unit-left a) | op-assoc a b c = refl

  ap-W-homomorphism : ∀{A B} (f : A → B) (x : A) → pure-W (f x) ≡ ap-W (pure-W f) (pure-W x)
  ap-W-homomorphism f x rewrite sym (unit-left {{QM}} mempty) = refl

  ap-W-interchange : ∀{A B} (u : Writer (A → B)) (x : A) → ap-W u (pure-W x) ≡ ap-W (pure-W λ f → f x) u
  ap-W-interchange (f , v) x rewrite sym (unit-left v) | sym (unit-right v) = refl

  fmap-is-pure-ap-W : ∀{A B} (f : A → B) (v : Writer A) → fmap-W f v ≡ ap-W (pure-W f) v
  fmap-is-pure-ap-W f (a , v) rewrite sym (unit-left v) = refl

  instance
    ApplicativePropsWriter : ApplicativeProps
    ApplicativePropsWriter = record
                               { <*>-composition = ap-W-composition
                               ; <*>-homomorphism = ap-W-homomorphism
                               ; <*>-interchange = ap-W-interchange
                               ; fmap-is-pure-<*> = fmap-is-pure-ap-W
                               }


  >>=-assoc-W : ∀{A B C}
              → (x : Writer A) → (f : A → Writer B) → (g : B → Writer C)
              → bind-W (bind-W x f) g ≡ bind-W x (λ y → bind-W (f y) g)
  >>=-assoc-W (a , v) f g with f a
  ... | b , u with g b
  ... | c , w rewrite op-assoc v u w = refl
  return->>=-right-id-W : ∀{A} → (x : Writer A) → x ≡ bind-W x pure-W
  return->>=-right-id-W (a , v) rewrite sym (unit-right v) = refl
  return->>=-left-id-W  : ∀{A B} → (x : A) → (f : A → Writer B)
                        → bind-W (pure-W x) f ≡ f x
  return->>=-left-id-W x f with f x
  ... | a , v rewrite sym (unit-left v) = refl
  ap-W-is-ap : ∀{A B} (x : Writer (A → B)) (y : Writer A)
             → ap-W x y ≡ bind-W x λ f → bind-W y λ a → pure-W (f a)
  ap-W-is-ap (f , v) (a , u) rewrite sym (unit-right u) = refl

  MonadPropsWriter : MonadProps
  MonadPropsWriter = record { >>=-assoc = >>=-assoc-W
                            ; return->>=-right-id = return->>=-right-id-W
                            ; return->>=-left-id = return->>=-left-id-W
                            ; <*>-is-ap = ap-W-is-ap
                            }



