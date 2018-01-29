module Crypto.Props where

open import ThesisPrelude
open import Crypto.Syntax
open import Algebra.FunExt
open import Utility.Product
open import Utility.Vector
  
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

fmap-embed-CE : ∀{A B B′}(f : B → B′)(ce : CryptoExpr A B)
              → fmap-CE f ce ≡ (ce >>>-CE embed-CE f)
fmap-embed-CE f (embed-CE g) = refl
fmap-embed-CE f (uniform-CE n ce) = cong (uniform-CE n) $ fmap-embed-CE f ce

cofmap-ext-CE : ∀{A A′ B} (f g : A → A′)
            → (∀ a → f a ≡ g a)
            → (ce : CryptoExpr A′ B)
            → cofmap-CE f ce ≡ cofmap-CE g ce
cofmap-ext-CE f g pf (embed-CE h) = cong embed-CE $ fun-ext (λ z → h (f z)) (λ z → h (g z)) (λ z → cong h (pf z))
cofmap-ext-CE f g pf (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-ext-CE (second f) (second g) (λ { (xs , a) → cong (_,_ xs) $ pf a}) ce

cofmap-second-id : ∀{A B C}(ce : CryptoExpr (C × A) B)
                 → cofmap-CE id ce ≡ cofmap-CE (second id) ce
cofmap-second-id = cofmap-ext-CE id (second id) (λ { (c , a) → refl })

cofmap-id-CE : ∀{A B} → (ce : CryptoExpr A B) → ce ≡ cofmap-CE id ce
cofmap-id-CE (embed-CE g) = refl
cofmap-id-CE (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-id-CE ce ⟨≡⟩ cofmap-second-id ce

cofmap-comp-CE : ∀{A A′ A′′ B} (g : A′ → A′′) (f : A → A′) (ce : CryptoExpr A′′ B) 
             → cofmap-CE (g ∘′ f) ce ≡ cofmap-CE f (cofmap-CE g ce)
cofmap-comp-CE g f (embed-CE h) = cong embed-CE $ fun-ext (λ z → h (g (f z))) (λ z → h (g (f z))) (λ a → refl) 
cofmap-comp-CE g f (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-ext-CE (second (g ∘′ f))
                                                                           (second g ∘′ second f)
                                                                           (λ { (xs , a) → refl })
                                                                           ce
                                                           ⟨≡⟩ cofmap-comp-CE (second g) (second f) ce

cofmap->>>-dist : ∀{A A′ B C}(f : A → A′)(E : CryptoExpr A′ B)(F : CryptoExpr B C)
                → (cofmap-CE f (E >>>-CE F)) ≡ (cofmap-CE f E >>>-CE F)
cofmap->>>-dist f (embed-CE g) F = sym $ cofmap-comp-CE g f F 
cofmap->>>-dist f (uniform-CE n E) F = cong (uniform-CE n) $ cofmap->>>-dist (second f) E F

id->>>-right-unit : ∀{A B}(E : CryptoExpr A B)
                  → E ≡ (E >>>-CE embed-CE id)
id->>>-right-unit (embed-CE g) = refl
id->>>-right-unit (uniform-CE n E) = cong (uniform-CE n) $ id->>>-right-unit E

id->>>-left-unit : ∀{A B}(E : CryptoExpr A B)
                 → E ≡ (embed-CE id >>>-CE E)
id->>>-left-unit (embed-CE g) = refl
id->>>-left-unit (uniform-CE n E) = cong (uniform-CE n) $ id->>>-left-unit E ⟨≡⟩ cofmap-ext-CE id (second id) (λ { (xs , a) → refl }) E

>>>-assoc : ∀{A B C D}(E : CryptoExpr A B)(F : CryptoExpr B C)(G : CryptoExpr C D)
          → (E >>>-CE F >>>-CE G) ≡ ((E >>>-CE F) >>>-CE G)
>>>-assoc (embed-CE g) F G = cofmap->>>-dist g F G
>>>-assoc (uniform-CE n E) F G = cong (uniform-CE n) $ >>>-assoc E F G

embed->>>-comp : ∀{A B C}(f : B → C)(g : A → B)
               → embed-CE (f ∘′ g) ≡ (embed-CE g >>>-CE embed-CE f)
embed->>>-comp f g = refl

{- Some generalisation of this should be provable.
rev-commute : ∀{A B C}(ce : CryptoExpr A B)
                  → fmap-CE (uncurry rev-pair) (first-CE ce) ≡ cofmap-CE (uncurry rev-pair) (second-CE ce) as CryptoExpr (A × C) (C × B)
rev-commute (embed-CE g) = cong embed-CE $ fun-ext (uncurry rev-pair ∘′ first g) (second g ∘′ uncurry rev-pair) (λ { (a , c) → refl })
rev-commute (uniform-CE n ce) = cong (uniform-CE n) $ {!!}
-}

embed-interchangeable : ∀{A A′ B B′}(f : A → B)(ce : CryptoExpr A′ B′)
                      → cofmap-CE (first f) (second-CE ce) ≡ (second-CE ce >>>-CE embed-CE (first f))
embed-interchangeable f (embed-CE g) = cong embed-CE $ fun-ext (second g ∘′ first f) (first f ∘′ second g) λ { (c , d) → refl }
embed-interchangeable f (uniform-CE n ce) = cong (uniform-CE n) $
  cofmap-CE (second (first f)) (cofmap-CE rev-first (second-CE ce))
    ≡⟨ cofmap-comp-CE rev-first (second (first f)) (second-CE ce) ⟩ʳ
  cofmap-CE (rev-first ∘′ second (first f)) (second-CE ce)
    ≡⟨ cofmap-ext-CE (rev-first ∘′ second (first f))
                     (first f ∘′ rev-first)
                     (λ { (xs , c , c′) → refl })
                     (second-CE ce) ⟩
  cofmap-CE (first f ∘′ rev-first) (second-CE ce)
    ≡⟨ cofmap-comp-CE (first f) rev-first (second-CE ce)  ⟩
  cofmap-CE rev-first (cofmap-CE (first f) (second-CE ce))
    ≡⟨ cong (cofmap-CE rev-first) (embed-interchangeable f ce) ⟩
  cofmap-CE rev-first (second-CE ce >>>-CE embed-CE (first f))
    ≡⟨ cofmap->>>-dist rev-first (second-CE ce) (embed-CE (first f)) ⟩
  cofmap-CE rev-first (second-CE ce) >>>-CE embed-CE (first f)
  ∎

{-
Due to this result, we cannot prove order-irrelevance on the expression level.
not-reversible : ¬ ((first-CE (uniform-expr′ 1) >>>-CE second-CE (uniform-expr′ 2)) ≡
                    (second-CE (uniform-expr′ 2) >>>-CE first-CE (uniform-expr′ 1)))
not-reversible ()

-}

