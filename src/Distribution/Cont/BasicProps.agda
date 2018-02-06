open import Probability.Class using (Probability)
module Distribution.Cont.BasicProps (Q : Set) {{QC : Probability Q}} where

open Probability QC
open import ThesisPrelude
open import Distribution.Class
open import Distribution.PropsClass
open import Distribution.Cont.Definition Q
open import Probability.Class
open import Algebra.FunExt

open import Algebra.FunctorProps ContDist

fmap-ext-CD : ∀{A B}(f g : A → B)
            → (∀ a → f a ≡ g a)
            → (ca : ContDist A)
            → fmap-CD f ca ≡ fmap-CD g ca
fmap-ext-CD f g eq ca rewrite fun-ext f g eq = refl

fmap-id-CD : ∀{A}(ca : ContDist A) → ca ≡ fmap-CD id ca
fmap-id-CD ca = refl

fmap-comp-CD : ∀{A B C}(g : B → C)(f : A → B)(ca : ContDist A)
             → fmap-CD (g ∘′ f) ca ≡ fmap-CD g (fmap-CD f ca)
fmap-comp-CD g f ca = refl

instance
  FunctorPropsContDist : FunctorProps
  FunctorPropsContDist = record { fmap-ext = fmap-ext-CD ; fmap-id = fmap-id-CD ; fmap-comp = fmap-comp-CD }

open import Algebra.ApplicativeProps ContDist
open import Algebra.MonadProps ContDist

instance
  postulate
    ApplicativePropsContDist : ApplicativeProps
    MonadPropsContDist : MonadProps
