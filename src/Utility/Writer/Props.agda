open import ThesisPrelude using (Monoid)
module Utility.Writer.Props {l} (Q : Set l) {{QM : Monoid Q}} where

open import ThesisPrelude
open import Utility.Product
open import Algebra.Monoid Q
open import Utility.Writer.Writer Q

fmap-W-ext : ∀{A B} (f g : A → B)
               → (∀ a → f a ≡ g a)
               → (x : Writer A)
               → over-fst f x ≡ over-fst g x
fmap-W-ext f g p (a , q) rewrite p a = refl

fmap-W-id : ∀{A}
              → (x : Writer A)
              → x ≡ over-fst id x
fmap-W-id (a , q) = refl 

fmap-W-comp : ∀{A B C} (g : B → C) (f : A → B) (x : Writer A)
                → over-fst (g ∘′ f) x ≡ over-fst g (over-fst f x)
fmap-W-comp g f (a , q) = refl

open import Algebra.FunctorProps Writer
instance
  FunctorPropsWriter : FunctorProps
  FunctorPropsWriter = record { fmap-ext = fmap-W-ext ; fmap-id = fmap-W-id ; fmap-comp = fmap-W-comp }

open import Algebra.ApplicativeProps Writer
open import Algebra.MonadProps Writer

module _ {{QP : MonoidProps}} where
  open MonoidProps QP
  mul-Writer-assoc : ∀{A} (p q : Q) (w : Writer A) → mul-Writer (p <> q) w ≡ mul-Writer p (mul-Writer q w) 
  mul-Writer-assoc p q (a , r) = cong (_,_ a) (sym (op-assoc p q r))

  mul-Writer-id : ∀{A} (w : Writer A) → w ≡ mul-Writer mempty w 
  mul-Writer-id (a , p) = cong (_,_ a) (unit-left p)

  ap-W-composition : ∀{A B C} (u : Writer (B → C)) (v : Writer (A → B)) (w : Writer A)
                  → ap-W u (ap-W v w) ≡ ap-W (ap-W (ap-W (pure-W _∘′_) u) v) w
  ap-W-composition (f , a) (g , b) (h , c)
    rewrite sym (unit-left a) | op-assoc a b c = refl

  ap-W-homomorphism : ∀{A B} (f : A → B) (x : A) → pure-W (f x) ≡ ap-W (pure-W f) (pure-W x)
  ap-W-homomorphism f x rewrite sym (unit-left mempty) = refl

  ap-W-interchange : ∀{A B} (u : Writer (A → B)) (x : A) → ap-W u (pure-W x) ≡ ap-W (pure-W λ f → f x) u
  ap-W-interchange (f , v) x rewrite sym (unit-left v) | sym (unit-right v) = refl

  fmap-is-pure-ap-W : ∀{A B} (f : A → B) (v : Writer A) → over-fst f v ≡ ap-W (pure-W f) v
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

  >>=-W-ext : ∀{A B} (x : Writer A) (f g : A → Writer B)
            → (∀ a → f a ≡ g a)
            → bind-W x f ≡ bind-W x g
  >>=-W-ext (a , q) f g pf with f a | g a | pf a
  >>=-W-ext (a , q) f g pf | b , p | .b , .p | refl = refl

  ap-W-is-ap : ∀{A B} (x : Writer (A → B)) (y : Writer A)
             → ap-W x y ≡ bind-W x λ f → bind-W y λ a → pure-W (f a)
  ap-W-is-ap (f , v) (a , u) rewrite sym (unit-right u) = refl

  MonadPropsWriter : MonadProps
  MonadPropsWriter = record { >>=-assoc = >>=-assoc-W
                            ; return->>=-right-id = return->>=-right-id-W
                            ; return->>=-left-id = return->>=-left-id-W
                            ; >>=-ext = >>=-W-ext
                            ; <*>-is-ap = ap-W-is-ap
                            }



