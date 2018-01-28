module Crypto.Props where

open import ThesisPrelude
open import Crypto.Syntax
open import Algebra.FunExt
  
fmap-ext-CE : ∀{A B B′} (f g : B → B′)
            → (∀ b → f b ≡ g b)
            → (ce : CryptoExpr A B)
            → fmap-CE f ce ≡ fmap-CE g ce
fmap-ext-CE f g pf (embed-CE h) = cong embed-CE $ fun-ext (λ z → f (h z)) (λ z → g (h z)) (λ z → pf (h z))
fmap-ext-CE f g pf (uniform-CE n ce) = cong (uniform-CE n) $ fmap-ext-CE f g pf ce

fmap-id-CE : ∀{A B} → (ce : CryptoExpr A B) → ce ≡ fmap-CE id ce
fmap-id-CE (embed-CE g) = refl
fmap-id-CE (uniform-CE n ce) = cong (uniform-CE n) (fmap-id-CE ce)

fmap-comp-CE : ∀{A B B′ B′′} (g : B′ → B′′) (f : B → B′) (ce : CryptoExpr A B) 
             → fmap-CE (g ∘′ f) ce ≡ fmap-CE g (fmap-CE f ce)
fmap-comp-CE g f (embed-CE h) = cong embed-CE $ fun-ext (λ z → g (f (h z))) (λ z → g (f (h z))) (λ z → refl)
fmap-comp-CE g f (uniform-CE n ce) = cong (uniform-CE n) $ fmap-comp-CE g f ce

open import Algebra.FunctorProps

instance
  FunctorPropsCryptoExpr : ∀{A} → FunctorProps (CryptoExpr A)
  FunctorPropsCryptoExpr = record { fmap-ext = fmap-ext-CE ; fmap-id = fmap-id-CE ; fmap-comp = fmap-comp-CE }

