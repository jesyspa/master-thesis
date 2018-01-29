module Crypto.Props where

open import ThesisPrelude
open import Crypto.Syntax
open import Algebra.FunExt
open import Utility.Product
open import Utility.Vector
  
fmap-ext-CE : ∀{O O′ A B B′} (f g : B → B′)
            → (∀ b → f b ≡ g b)
            → (ce : CryptoExpr O O′ A B)
            → fmap-CE f ce ≡ fmap-CE g ce
fmap-ext-CE f g pf (embed-CE h) = cong embed-CE $ fun-ext (λ z → f (h z)) (λ z → g (h z)) (λ z → pf (h z))
fmap-ext-CE f g pf (uniform-CE n ce) = cong (uniform-CE n) $ fmap-ext-CE f g pf ce
fmap-ext-CE f g pf (addOracle-CE h ce) = cong (addOracle-CE h) $ fmap-ext-CE f g pf ce
fmap-ext-CE f g pf (callOracle-CE p ce cf) = cong (callOracle-CE p ce) $ fmap-ext-CE f g pf cf

fmap-id-CE : ∀{O O′ A B} → (ce : CryptoExpr O O′ A B) → ce ≡ fmap-CE id ce
fmap-id-CE (embed-CE g) = refl
fmap-id-CE (uniform-CE n ce) = cong (uniform-CE n) $ fmap-id-CE ce
fmap-id-CE (addOracle-CE g ce) = cong (addOracle-CE g) $ fmap-id-CE ce
fmap-id-CE (callOracle-CE p ce cf) = cong (callOracle-CE p ce) $ fmap-id-CE cf

fmap-comp-CE : ∀{O O′ A B B′ B′′} (g : B′ → B′′) (f : B → B′) (ce : CryptoExpr O O′ A B) 
             → fmap-CE (g ∘′ f) ce ≡ fmap-CE g (fmap-CE f ce)
fmap-comp-CE g f (embed-CE h) = cong embed-CE $ fun-ext (λ z → g (f (h z))) (λ z → g (f (h z))) (λ z → refl)
fmap-comp-CE g f (uniform-CE n ce) = cong (uniform-CE n) $ fmap-comp-CE g f ce
fmap-comp-CE g f (addOracle-CE h ce) = cong (addOracle-CE h) $ fmap-comp-CE g f ce
fmap-comp-CE g f (callOracle-CE p ce cf) = cong (callOracle-CE p ce) $ fmap-comp-CE g f cf

open import Algebra.FunctorProps

instance
  FunctorPropsCryptoExpr : ∀{O O′ A} → FunctorProps (CryptoExpr O O′ A)
  FunctorPropsCryptoExpr = record { fmap-ext = fmap-ext-CE ; fmap-id = fmap-id-CE ; fmap-comp = fmap-comp-CE }

fmap-embed-CE : ∀{O O′ A B B′}(f : B → B′)(ce : CryptoExpr O O′ A B)
              → fmap-CE f ce ≡ (ce >>>-CE embed-CE f)
fmap-embed-CE f (embed-CE g) = refl
fmap-embed-CE f (uniform-CE n ce) = cong (uniform-CE n) $ fmap-embed-CE f ce
fmap-embed-CE f (addOracle-CE g ce) = cong (addOracle-CE g) $ fmap-embed-CE f ce
fmap-embed-CE f (callOracle-CE p ce cf) = cong (callOracle-CE p ce) $ fmap-embed-CE f cf

cofmap-ext-CE : ∀{O O′ A A′ B} (f g : A → A′)
            → (∀ a → f a ≡ g a)
            → (ce : CryptoExpr O O′ A′ B)
            → cofmap-CE f ce ≡ cofmap-CE g ce
cofmap-ext-CE f g pf (embed-CE h) = cong embed-CE $ fun-ext (λ z → h (f z)) (λ z → h (g z)) (λ z → cong h (pf z))
cofmap-ext-CE f g pf (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-ext-CE (second f) (second g) (λ { (xs , a) → cong (_,_ xs) $ pf a}) ce
cofmap-ext-CE f g pf (addOracle-CE h ce) = cong (addOracle-CE h) $ cofmap-ext-CE f g pf ce
cofmap-ext-CE f g pf (callOracle-CE p ce cf) = cong (λ e → callOracle-CE p e cf) $ cofmap-ext-CE f g pf ce

cofmap-second-id : ∀{O O′ A B C}(ce : CryptoExpr O O′ (C × A) B)
                 → cofmap-CE id ce ≡ cofmap-CE (second id) ce
cofmap-second-id = cofmap-ext-CE id (second id) (λ { (c , a) → refl })

cofmap-id-CE : ∀{O O′ A B} → (ce : CryptoExpr O O′ A B) → ce ≡ cofmap-CE id ce
cofmap-id-CE (embed-CE g) = refl
cofmap-id-CE (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-id-CE ce ⟨≡⟩ cofmap-second-id ce
cofmap-id-CE (addOracle-CE g ce) = cong (addOracle-CE g) $ cofmap-id-CE ce
cofmap-id-CE (callOracle-CE p ce cf) = cong (λ e → callOracle-CE p e cf) $ cofmap-id-CE ce

cofmap-comp-CE : ∀{O O′ A A′ A′′ B} (g : A′ → A′′) (f : A → A′) (ce : CryptoExpr O O′ A′′ B) 
             → cofmap-CE (g ∘′ f) ce ≡ cofmap-CE f (cofmap-CE g ce)
cofmap-comp-CE g f (embed-CE h) = cong embed-CE $ fun-ext (λ z → h (g (f z))) (λ z → h (g (f z))) (λ a → refl) 
cofmap-comp-CE g f (uniform-CE n ce) = cong (uniform-CE n) $ cofmap-ext-CE (second (g ∘′ f))
                                                                           (second g ∘′ second f)
                                                                           (λ { (xs , a) → refl })
                                                                           ce
                                                           ⟨≡⟩ cofmap-comp-CE (second g) (second f) ce
cofmap-comp-CE g f (addOracle-CE h ce) = cong (addOracle-CE h) $ cofmap-comp-CE g f ce 
cofmap-comp-CE g f (callOracle-CE p ce cf) = cong (λ e → callOracle-CE p e cf) $ cofmap-comp-CE g f ce

cofmap->>>-dist : ∀{O O′ O′′ A A′ B C}(f : A → A′)(E : CryptoExpr O O′ A′ B)(F : CryptoExpr O′ O′′ B C)
                → (cofmap-CE f (E >>>-CE F)) ≡ (cofmap-CE f E >>>-CE F)
cofmap->>>-dist f (embed-CE g) F = sym $ cofmap-comp-CE g f F 
cofmap->>>-dist f (uniform-CE n E) F = cong (uniform-CE n) $ cofmap->>>-dist (second f) E F
cofmap->>>-dist f (addOracle-CE g ce) F = cong (addOracle-CE g) $ cofmap->>>-dist f ce F
cofmap->>>-dist f (callOracle-CE p ce cf) F = refl

fmap-cofmap-swap : ∀{O O′ A A′ B B′}(f : A → A′)(g : B → B′)(E : CryptoExpr O O′ A′ B)
                 → cofmap-CE f (fmap-CE g E) ≡ fmap-CE g (cofmap-CE f E)
fmap-cofmap-swap f g (embed-CE h) = refl
fmap-cofmap-swap f g (uniform-CE n E) = cong (uniform-CE n) $ fmap-cofmap-swap (second f) g E
fmap-cofmap-swap f g (addOracle-CE h E) = cong (addOracle-CE h) $ fmap-cofmap-swap f g E
fmap-cofmap-swap f g (callOracle-CE p E E′) = refl

id->>>-right-unit : ∀{O O′ A B}(E : CryptoExpr O O′ A B)
                  → E ≡ (E >>>-CE embed-CE id)
id->>>-right-unit (embed-CE g) = refl
id->>>-right-unit (uniform-CE n E) = cong (uniform-CE n) $ id->>>-right-unit E
id->>>-right-unit (addOracle-CE g ce) = cong (addOracle-CE g) $ id->>>-right-unit ce 
id->>>-right-unit (callOracle-CE p ce cf) = cong (callOracle-CE p ce) $ id->>>-right-unit cf

id->>>-left-unit : ∀{O O′ A B}(E : CryptoExpr O O′ A B)
                 → E ≡ (embed-CE id >>>-CE E)
id->>>-left-unit (embed-CE g) = refl
id->>>-left-unit (uniform-CE n E) = cong (uniform-CE n) $ id->>>-left-unit E ⟨≡⟩ cofmap-ext-CE id (second id) (λ { (xs , a) → refl }) E
id->>>-left-unit (addOracle-CE g E) = cong (addOracle-CE g) $ id->>>-left-unit E
id->>>-left-unit (callOracle-CE p E E′) = cong (λ e → callOracle-CE p e E′) $ id->>>-left-unit E

>>>-assoc : ∀{O₀ O₁ O₂ O₃ A B C D}(E : CryptoExpr O₀ O₁ A B)(F : CryptoExpr O₁ O₂ B C)(G : CryptoExpr O₂ O₃ C D)
          → (E >>>-CE F >>>-CE G) ≡ ((E >>>-CE F) >>>-CE G)
>>>-assoc (embed-CE g) F G = cofmap->>>-dist g F G
>>>-assoc (uniform-CE n E) F G = cong (uniform-CE n) $ >>>-assoc E F G
>>>-assoc (addOracle-CE g E) F G = cong (addOracle-CE g) $ >>>-assoc E F G
>>>-assoc (callOracle-CE p E E′) F G = cong (callOracle-CE p E) $ >>>-assoc E′ F G

{- Some generalisation of this should be provable.
rev-commute : ∀{A B C}(ce : CryptoExpr A B)
                  → fmap-CE (uncurry rev-pair) (first-CE ce) ≡ cofmap-CE (uncurry rev-pair) (second-CE ce) as CryptoExpr (A × C) (C × B)
rev-commute (embed-CE g) = cong embed-CE $ fun-ext (uncurry rev-pair ∘′ first g) (second g ∘′ uncurry rev-pair) (λ { (a , c) → refl })
rev-commute (uniform-CE n ce) = cong (uniform-CE n) $ {!!}
-}

embed-interchangeable : ∀{O O′ A A′ B B′}(f : A → B)(ce : CryptoExpr O O′ A′ B′)
                      → cofmap-CE (first f) (second-CE ce) ≡ fmap-CE (first f) (second-CE ce)
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
  cofmap-CE rev-first (fmap-CE (first f) (second-CE ce))
    ≡⟨ fmap-cofmap-swap rev-first (first f) (second-CE ce) ⟩
  fmap-CE (first f) (cofmap-CE rev-first (second-CE ce))
  ∎
embed-interchangeable f (addOracle-CE g ce) = cong (addOracle-CE g) $ embed-interchangeable f ce
embed-interchangeable f (callOracle-CE p ce cf) =
  callOracle-CE p (cofmap-CE (first f) (fmap-CE rev-first (second-CE ce))) (cofmap-CE rev-first (second-CE cf))
    ≡⟨ {!!} ⟩
  callOracle-CE p (fmap-CE rev-first (second-CE ce)) (fmap-CE (first f) (cofmap-CE rev-first (second-CE cf)))
  ∎

{-
Due to this result, we cannot prove order-irrelevance on the expression level.
not-reversible : ¬ ((first-CE (uniform-expr′ 1) >>>-CE second-CE (uniform-expr′ 2)) ≡
                    (second-CE (uniform-expr′ 2) >>>-CE first-CE (uniform-expr′ 1)))
not-reversible ()

-}

