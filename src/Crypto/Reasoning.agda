import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.Reasoning (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Valuation F
open import Probability.Class
open import Utility.Vector
open import Utility.Bool
open import Algebra.ApplicativeProps F
open import Algebra.MonadProps F
open import Distribution.Class
open import Distribution.PropsClass F
open import Distribution.Reasoning F
open import Crypto.Props
open import Algebra.FunctorProps CryptoExpr using () renaming (FunctorProps to CFProps)
open import Algebra.MonadProps CryptoExpr using () renaming (MonadProps to CMProps)
open import Crypto.ValuationProps F

open DistMonad DMF
open DistMonadProps DMPF 
open MonadProps is-monad
open ApplicativeProps aprops
open Probability probability-super

cong->>= : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A)(F G : A → CryptoExpr B)
         → (∀ a → ⟦ F a ⟧ ≡D ⟦ G a ⟧)
         → ⟦ E >>= F ⟧ ≡D ⟦ E >>= G ⟧
cong->>= E F G eq =
  ⟦ E >>= F ⟧
    ≡D⟨ bind-interpretation E F ⟩ˡʳ
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ F
    ≡D⟨ >>=-D-ext ⟦ E ⟧ (⟦_⟧ ∘′ F) (⟦_⟧ ∘′ G) eq  ⟩
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ G
    ≡D⟨  bind-interpretation E G ⟩ˡ
  ⟦ E >>= G ⟧
  ∎D

cong->>=ˡ : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A)(F G : A → CryptoExpr B)
          → (∀ a → ⟦ F a ⟧ ≡ ⟦ G a ⟧)
          → ⟦ E >>= F ⟧ ≡ ⟦ E >>= G ⟧
cong->>=ˡ E F G eq =
  ⟦ E >>= F ⟧
    ≡⟨ bind-interpretation E F ⟩ʳ
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ F
    ≡⟨ >>=-ext ⟦ E ⟧ (⟦_⟧ ∘′ F) (⟦_⟧ ∘′ G) eq  ⟩
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ G
    ≡⟨ bind-interpretation E G ⟩
  ⟦ E >>= G ⟧
  ∎
  

interchange-interpretation : ∀{A B C}{{_ : Eq C}}(EA : CryptoExpr A)(EB : CryptoExpr B)
                              (f : A → B → CryptoExpr C)
                           → ⟦ (EA >>= λ a → EB >>= f a) ⟧ ≡D ⟦ (EB >>= λ b → EA >>= λ a → f a b) ⟧ 
interchange-interpretation {C = C} EA EB f =
  ⟦ (EA >>= λ a → EB >>= f a) ⟧
    ≡D⟨ lem EA EB f ⟩ˡ
  (⟦ EA ⟧ >>= λ a → ⟦ EB ⟧ >>= λ b → ⟦ f a b ⟧)
    ≡D⟨ interchange ⟦ EA ⟧ ⟦ EB ⟧ (λ a b → ⟦ f a b ⟧) ⟩
  (⟦ EB ⟧ >>= λ b → ⟦ EA ⟧ >>= λ a → ⟦ f a b ⟧)
    ≡D⟨ lem EB EA (flip f) ⟩ˡʳ
  ⟦ (EB >>= λ b → EA >>= λ a → f a b) ⟧ 
  ∎D
  where
    lem : ∀{A′ B′}(EA′ : CryptoExpr A′)(EB′ : CryptoExpr B′)(f′ : A′ → B′ → CryptoExpr C)
        → ⟦ (EA′ >>= λ a → EB′ >>= f′ a) ⟧ ≡ (⟦ EA′ ⟧ >>= λ a → ⟦ EB′ ⟧ >>= λ b → ⟦ f′ a b ⟧)
    lem EA′ EB′ f′ =
      ⟦ (EA′ >>= λ a → EB′ >>= f′ a) ⟧
        ≡⟨ bind-interpretation EA′ (λ a → EB′ >>= f′ a) ⟩ʳ
      (⟦ EA′ ⟧ >>= λ a → ⟦ EB′ >>= f′ a ⟧)
        ≡⟨ >>=-ext ⟦ EA′ ⟧
                    (λ a → ⟦ EB′ >>= f′ a ⟧)
                    (λ a → ⟦ EB′ ⟧ >>= λ b → ⟦ f′ a b ⟧)
                    (λ a → sym (bind-interpretation EB′ (f′ a))) ⟩
      (⟦ EA′ ⟧ >>= λ a → ⟦ EB′ ⟧ >>= λ b → ⟦ f′ a b ⟧)
      ∎

irrelevance-interpretation : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A)(F : CryptoExpr B)
                    → ⟦ F ⟧ ≡D ⟦ E >>= const F ⟧
irrelevance-interpretation (returnCE a) F = sample-equality λ b → refl
irrelevance-interpretation (uniformCE n cont) F = sample-equality λ b → 
  sample ⟦ F ⟧ b
    ≡⟨ flip sample-invariant b $ irrelevance n ⟦ F ⟧  ⟩
  sample (uniform n >>= (λ xs → ⟦ F ⟧)) b
    ≡⟨ flip sample-invariant b
                           $ >>=-D-ext (uniform n)
                                       (const ⟦ F ⟧)
                                       (λ xs → ⟦ cont xs >>= const F ⟧)
                                       (λ xs → irrelevance-interpretation (cont xs) F) ⟩
  sample (uniform n >>= (λ xs → ⟦ cont xs >>= const F ⟧)) b
  ∎
