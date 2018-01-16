module Crypto.Props where

open import ThesisPrelude
open import Crypto.Syntax
open import Algebra.FunctorProps CryptoExpr
open import Algebra.ApplicativeProps CryptoExpr
open import Algebra.MonadProps CryptoExpr
open import Algebra.FunExt

fmap-ext-CE : ∀{A B} (f g : A → B)
            → (∀ a → f a ≡ g a)
            → (x : CryptoExpr A)
            → fmap-CE f x ≡ fmap-CE g x
fmap-ext-CE f g pf (returnCE a) rewrite pf a = refl
fmap-ext-CE f g pf (uniformCE n cont) = cong (uniformCE n) (fun-ext (fmap-CE f ∘′ cont) (fmap-CE g ∘′ cont) λ a → fmap-ext-CE f g pf (cont a)) 

fmap-id-CE : ∀{A} → (x : CryptoExpr A) → x ≡ fmap-CE id x
fmap-id-CE (returnCE a) = refl
fmap-id-CE (uniformCE n cont) = cong (uniformCE n) (fun-ext cont (fmap-CE id ∘′ cont) λ a → fmap-id-CE (cont a))

fmap-comp-CE : ∀{A B C} (g : B → C) (f : A → B) (x : CryptoExpr A) 
             → fmap-CE (g ∘′ f) x ≡ fmap-F g (fmap-CE f x)
fmap-comp-CE g f (returnCE a) = refl
fmap-comp-CE g f (uniformCE n cont) = cong (uniformCE n) (fun-ext (fmap-CE (g ∘ f) ∘′ cont)
                                                                  (fmap-CE g ∘′ fmap-CE f ∘′ cont)
                                                                  λ a → fmap-comp-CE g f (cont a)) 

instance
  FunctorPropsCryptoExpr : FunctorProps
  FunctorPropsCryptoExpr = record { fmap-ext = fmap-ext-CE ; fmap-id = fmap-id-CE ; fmap-comp = fmap-comp-CE }

open FunctorProps FunctorPropsCryptoExpr

postulate
  ApplicativePropsCryptoExpr : ApplicativeProps
  MonadPropsCryptoExpr : MonadProps
