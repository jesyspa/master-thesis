import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.ValuationProps (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

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
open import Crypto.Props
open import Algebra.FunctorProps CryptoExpr using () renaming (FunctorProps to CFProps)
open import Algebra.MonadProps CryptoExpr using () renaming (MonadProps to CMProps)

open DistMonad DMF
open DistMonadProps DMPF 
open MonadProps is-monad
open ApplicativeProps aprops
open Probability probability-super

uniform-dist-interpretation : ∀ n → uniform n ≡ ⟦ uniform-expr n ⟧
uniform-dist-interpretation n = return->>=-right-id (uniform n)

fmap-interpretation : ∀{A B} (f : A → B) (E : CryptoExpr A)
                    → fmap f ⟦ E ⟧ ≡ ⟦ fmap f E ⟧
fmap-interpretation f (returnCE x) = sym (fmap-of-pure f x)
fmap-interpretation f (uniformCE n cont) =
  fmap f (uniform n >>= (λ y → ⟦ cont y ⟧))
    ≡⟨ fmap-bind f (uniform n) (⟦_⟧ ∘′ cont) ⟩
  uniform n >>= (λ y → fmap f ⟦ cont y ⟧)
    ≡⟨ >>=-ext (uniform n) (fmap f ∘′ ⟦_⟧ ∘′ cont) (⟦_⟧ ∘′ fmap f ∘ cont)
               (λ a → fmap-interpretation f (cont a)) ⟩
  uniform n >>= (λ y → ⟦ fmap f (cont y) ⟧)
  ∎

bind-interpretation : ∀{A B}(E : CryptoExpr A)(F : A → CryptoExpr B)
                    → (⟦ E ⟧ >>= λ e → ⟦ F e ⟧) ≡ ⟦ E >>= F ⟧
bind-interpretation (returnCE a) F       = return->>=-left-id a (⟦_⟧ ∘′ F)
bind-interpretation (uniformCE n cont) F =
  uniform n >>= (⟦_⟧ ∘′ cont) >>= ⟦_⟧ ∘′ F
    ≡⟨ >>=-assoc (uniform n) (⟦_⟧ ∘′ cont) (⟦_⟧ ∘′ F) ⟩
  uniform n >>= (λ z → ⟦ cont z ⟧ >>= λ e → ⟦ F e ⟧)
    ≡⟨ >>=-ext (uniform n)
               (λ z → ⟦ cont z ⟧ >>= λ e → ⟦ F e ⟧)
               (λ z → ⟦ cont z >>= F ⟧)
               (λ z → bind-interpretation (cont z) F) ⟩
  uniform n >>= (λ z → ⟦ cont z >>= F ⟧)
  ∎

bind-const-interpretation : ∀{A B}(E : CryptoExpr A)(F : CryptoExpr B)
                    → (⟦ E ⟧ >>= const ⟦ F ⟧) ≡ ⟦ E >>= const F ⟧
bind-const-interpretation E F = bind-interpretation E (const F)

coin-interpretation : coin ≡ ⟦ coin-expr ⟧
coin-interpretation = cong (fmap head) (uniform-dist-interpretation 1) ⟨≡⟩ fmap-interpretation head (uniform-expr 1)

coin-sample : ∀ b → negpow2 1 ≡ sample ⟦ coin-expr ⟧ b
coin-sample b =
  negpow2 1
    ≡⟨ uniform-is-uniform 1 (b ∷ []) ⟩
  sample (uniform 1) (b ∷ [])
    ≡⟨ cong (λ e → sample e (b ∷ [])) (uniform-dist-interpretation 1) ⟩ 
  sample ⟦ uniform-expr 1 ⟧ (b ∷ [])
    ≡⟨ injection-invariant head head1-Inj ⟦ uniform-expr 1 ⟧ ((b ∷ [])) ⟩
  sample (fmap head ⟦ uniform-expr 1 ⟧) b
    ≡⟨ cong (λ e → sample e b) (fmap-interpretation head (uniform-expr 1)) ⟩
  sample ⟦ fmap head (uniform-expr 1) ⟧ b
    ≡⟨ refl ⟩
  sample ⟦ coin-expr ⟧ b
  ∎

coin-sample-2 : ∀ b → ⟦ coin-expr ⟧ ≡D ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧
coin-sample-2 b = sample-equality λ a → 
  sample ⟦ coin-expr ⟧ a
    ≡⟨ cong (λ e → sample e a) coin-interpretation ⟩ʳ
  sample coin a
    ≡⟨ sample-invariant (coin-bijection-invariant (nxor b) (nxor-Bij b)) a ⟩
  sample (fmap (nxor b) coin) a
    ≡⟨ cong (λ e → sample e a) lem ⟩
  sample ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧ a
  ∎
  where lem : fmap (nxor b) coin ≡ ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧
        lem = 
          fmap (nxor b) coin
            ≡⟨ cong (fmap (nxor b)) coin-interpretation ⟩
          fmap (nxor b) ⟦ coin-expr ⟧
            ≡⟨ fmap-interpretation (nxor b) coin-expr ⟩
          ⟦ fmap (nxor b) coin-expr ⟧
            ≡⟨ cong ⟦_⟧ (CMProps.return-simplify MonadPropsCryptoExpr (nxor b) coin-expr) ⟩
          ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧
          ∎

coin-sample-2-interpretation : ∀ b → ⟦ coin-expr ⟧ ≡D (⟦ coin-expr ⟧ >>= λ b′ → ⟦ return (nxor b b′) ⟧)
coin-sample-2-interpretation b = sample-equality λ a →
  sample ⟦ coin-expr ⟧ a
    ≡⟨ flip sample-invariant a $ coin-sample-2 b ⟩
  sample ⟦ (coin-expr >>= λ b′ → return (nxor b b′)) ⟧ a
    ≡⟨ cong (λ e → sample e a) $ bind-interpretation coin-expr (λ b′ → return (nxor b b′)) ⟩ʳ
  sample (⟦ coin-expr ⟧ >>= λ b′ → ⟦ return (nxor b b′) ⟧) a
  ∎

coin-sample-3 : ∀{A} (E : CryptoExpr A) → ⟦ coin-expr ⟧ ≡D ⟦ (E >>= λ _ → coin-expr) ⟧
coin-sample-3 (returnCE a) = sample-equality λ x → refl
coin-sample-3 (uniformCE n cont) rewrite sym coin-interpretation = sample-equality λ a →
  sample coin a
    ≡⟨ sample-invariant (irrelevance n coin ) a ⟩
  sample (uniform n >>= λ xs → coin) a
    ≡⟨ cong (λ e → sample e a) (>>=-ext (uniform n) (const coin) (const ⟦ coin-expr ⟧) λ xs → coin-interpretation) ⟩
  sample (uniform n >>= λ xs → ⟦ coin-expr ⟧) a
    ≡⟨ sample-invariant (>>=-D-ext (uniform n)
                                   (λ _ → ⟦ coin-expr ⟧)
                                   (λ xs → ⟦ (cont xs >>= λ _ → coin-expr) ⟧ )
                                   (λ xs → coin-sample-3 (cont xs))) 
                        a ⟩
  sample (uniform n >>= λ xs → ⟦ (cont xs >>= λ _ → coin-expr) ⟧) a
  ∎

coin-sample-3-interpretation : ∀{A}(E : CryptoExpr A)
                             → ⟦ coin-expr ⟧ ≡D (⟦ E ⟧ >>= const ⟦ coin-expr ⟧)
coin-sample-3-interpretation E = sample-equality λ b →
  sample ⟦ coin-expr ⟧ b
    ≡⟨ (flip sample-invariant b $ coin-sample-3 E ) ⟩
  sample (⟦ E >>= const coin-expr ⟧) b
    ≡⟨ cong (λ e → sample e b) $ bind-interpretation E (const coin-expr) ⟩ʳ
  sample (⟦ E ⟧ >>= const ⟦ coin-expr ⟧) b
  ∎

general-irrelevance : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A)(F : CryptoExpr B)
                    → ⟦ F ⟧ ≡D ⟦ E >>= const F ⟧
general-irrelevance (returnCE a) F = sample-equality λ b → refl
general-irrelevance (uniformCE n cont) F = sample-equality λ b → 
  sample ⟦ F ⟧ b
    ≡⟨ flip sample-invariant b $ irrelevance n ⟦ F ⟧  ⟩
  sample (uniform n >>= (λ xs → ⟦ F ⟧)) b
    ≡⟨ flip sample-invariant b
                           $ >>=-D-ext (uniform n)
                                       (const ⟦ F ⟧)
                                       (λ xs → ⟦ cont xs >>= const F ⟧)
                                       (λ xs → general-irrelevance (cont xs) F) ⟩
  sample (uniform n >>= (λ xs → ⟦ cont xs >>= const F ⟧)) b
  ∎

general-irrelevance-interpretation : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A)(F : CryptoExpr B)
                                → ⟦ F ⟧ ≡D (⟦ E ⟧ >>= const ⟦ F ⟧)
general-irrelevance-interpretation E F = sample-equality λ b →
  sample ⟦ F ⟧ b
    ≡⟨ flip sample-invariant b (general-irrelevance E F) ⟩
  sample ⟦ E >>= const F ⟧ b
    ≡⟨ cong (λ e → sample e b) (bind-const-interpretation E F)  ⟩ʳ
  sample (⟦ E ⟧ >>= const ⟦ F ⟧) b
  ∎
