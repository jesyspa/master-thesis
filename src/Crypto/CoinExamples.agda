import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.CoinExamples (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

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
open import Crypto.Reasoning F

open DistMonad DMF
open DistMonadProps DMPF 
open MonadProps is-monad
open ApplicativeProps aprops
open Probability probability-super

coin-sample : ∀ b → negpow2 1 ≡ sample ⟦ coin-expr ⟧ b
coin-sample b = coin-is-fair b ⟨≡⟩ sample-invariant-at b (lift-D-eq coin-interpretation)

coin-sample-2 : ∀ b → ⟦ coin-expr ⟧ ≡D ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧
coin-sample-2 b =
  ⟦ coin-expr ⟧
    ≡D⟨ coin-interpretation ⟩ˡʳ
  coin
    ≡D⟨ coin-bijection-invariant (nxor b) (nxor-Bij b) ⟩
  fmap (nxor b) coin
    ≡D⟨ lem ⟩ˡ
  ⟦ coin-expr >>= (λ b′ → return (nxor b b′)) ⟧
  ∎D
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

coin-sample-3 : ∀{A} (E : CryptoExpr A) → ⟦ coin-expr ⟧ ≡D ⟦ (E >>= λ _ → coin-expr) ⟧
coin-sample-3 (returnCE a) = sample-equality λ x → refl
coin-sample-3 (uniformCE n cont) =
  ⟦ coin-expr ⟧
    ≡D⟨ irrelevance n ⟦ coin-expr ⟧ ⟩
  (uniform n >>= λ xs → ⟦ coin-expr ⟧)
    ≡D⟨ >>=-D-ext (uniform n)
                  (λ _ → ⟦ coin-expr ⟧)
                  (λ xs → ⟦ (cont xs >>= λ _ → coin-expr) ⟧)
                  (λ xs → coin-sample-3 (cont xs)) ⟩
  (uniform n >>= λ xs → ⟦ (cont xs >>= λ _ → coin-expr) ⟧)
  ∎D
