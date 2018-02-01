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
open import Algebra.Function
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

congl->>= : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}(E F : CryptoExpr A)(G : A → CryptoExpr B)
          → ⟦ E ⟧ ≡D ⟦ F ⟧
          → ⟦ E >>= G ⟧ ≡D ⟦ F >>= G ⟧
congl->>= E F G eq =
  ⟦ E >>= G ⟧
    ≡D⟨ bind-interpretation E G ⟩ˡʳ
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ G
    ≡D⟨ >>=-D-inv ⟦ E ⟧ ⟦ F ⟧ (⟦_⟧ ∘′ G) eq ⟩
  ⟦ F ⟧ >>= ⟦_⟧ ∘′ G
    ≡D⟨ bind-interpretation F G ⟩ˡ
  ⟦ F >>= G ⟧
  ∎D

congl->>=ˡ : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}(E F : CryptoExpr A)(G : A → CryptoExpr B)
          → ⟦ E ⟧ ≡ ⟦ F ⟧
          → ⟦ E >>= G ⟧ ≡ ⟦ F >>= G ⟧
congl->>=ˡ E F G eq =
  ⟦ E >>= G ⟧
    ≡⟨ bind-interpretation E G ⟩ʳ
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ G
    ≡⟨ cong (λ e → e >>= ⟦_⟧ ∘′ G) eq ⟩
  ⟦ F ⟧ >>= ⟦_⟧ ∘′ G
    ≡⟨ bind-interpretation F G ⟩
  ⟦ F >>= G ⟧
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

if-cong : ∀{A}{{_ : Eq A}}(b : Bool)(E E′ F F′ : CryptoExpr A)
        → (⟦ E ⟧ ≡D ⟦ E′ ⟧) → (⟦ F ⟧ ≡D ⟦ F′ ⟧)
        → ⟦( if b then E else F )⟧ ≡D ⟦( if b then E′ else F′ )⟧
if-cong false E E′ F F′ pE pF = pF
if-cong true E E′ F F′ pE pF = pE

uniform-bijection-invariant-interpretation : ∀ n (f : BitVec n → BitVec n)
                                           → Bijective f
                                           → ⟦ uniform-expr n ⟧ ≡D ⟦ fmap f (uniform-expr n) ⟧
uniform-bijection-invariant-interpretation n f pf =
  ⟦ uniform-expr n ⟧
    ≡D⟨ uniform-dist-interpretation n ⟩ˡʳ
  uniform n
    ≡D⟨ uniform-bijection-invariant n f pf ⟩
  fmap f (uniform n)
    ≡D⟨ cong (fmap f) (uniform-dist-interpretation n) ⟩ˡ
  fmap f ⟦ uniform-expr n ⟧
    ≡D⟨ fmap-interpretation f (uniform-expr n) ⟩ˡ
  ⟦ fmap f (uniform-expr n) ⟧
  ∎D

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
