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

bind-interpretation : ∀{A B}(F : A → CryptoExpr B)(E : CryptoExpr A)
                    → (⟦ E ⟧ >>= λ e → ⟦ F e ⟧) ≡ ⟦ E >>= F ⟧
bind-interpretation F (returnCE a) = return->>=-left-id a (⟦_⟧ ∘′ F)
bind-interpretation F (uniformCE n cont) =
  uniform n >>= (⟦_⟧ ∘′ cont) >>= ⟦_⟧ ∘′ F
    ≡⟨ >>=-assoc (uniform n) (⟦_⟧ ∘′ cont) (⟦_⟧ ∘′ F) ⟩
  uniform n >>= (λ z → ⟦ cont z ⟧ >>= λ e → ⟦ F e ⟧)
    ≡⟨ >>=-ext (uniform n)
               (λ z → ⟦ cont z ⟧ >>= λ e → ⟦ F e ⟧)
               (λ z → ⟦ cont z >>= F ⟧)
               (λ z → bind-interpretation F (cont z)) ⟩
  uniform n >>= (λ z → ⟦ cont z >>= F ⟧)
  ∎

coin-interpretation : coin ≡ ⟦ coin-expr ⟧
coin-interpretation = cong (fmap head) (uniform-dist-interpretation 1) ⟨≡⟩ fmap-interpretation head (uniform-expr 1)

