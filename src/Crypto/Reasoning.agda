import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.Reasoning (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Valuation F
open import Probability.Class
open import Utility.Vector
open import Utility.Product
open import Utility.Bool
open import Algebra.ApplicativeProps F
open import Algebra.MonadProps F
open import Distribution.Class
open import Distribution.PropsClass F
open import Distribution.Reasoning F
open import Crypto.Props
--open import Algebra.FunctorProps CryptoExpr using () renaming (FunctorProps to CFProps)
open import Crypto.ValuationProps F 

open DistMonad DMF
open DistMonadProps DMPF 
open MonadProps is-monad
open ApplicativeProps aprops
open Probability probability-super

cong->>>-right : ∀{A B C}{{_ : Eq C}}(E : CryptoExpr A B)(F G : CryptoExpr B C)
         → (∀ b → ⟦ F ⟧ b ≡D ⟦ G ⟧ b)
         → (a : A) → ⟦ E >>>-CE F ⟧ a ≡D ⟦ E >>>-CE G ⟧ a
cong->>>-right E F G eq a =
  ⟦ E >>>-CE F ⟧ a
    ≡D⟨ comp-interpretation E F a ⟩ˡʳ
  ⟦ E ⟧ a >>= ⟦ F ⟧
    ≡D⟨ >>=-D-ext (⟦ E ⟧ a) ⟦ F ⟧ ⟦ G ⟧ eq ⟩
  ⟦ E ⟧ a >>= ⟦ G ⟧
    ≡D⟨ comp-interpretation E G a ⟩ˡ
  ⟦ E >>>-CE G ⟧ a
  ∎D

{-
cong->>=ˡ : ∀{A B}{{_ : Eq B}}(E : CryptoExpr A){F G : A → CryptoExpr B}
          → (∀ a → ⟦ F a ⟧ ≡ ⟦ G a ⟧)
          → ⟦ E >>= F ⟧ ≡ ⟦ E >>= G ⟧
cong->>=ˡ E {F} {G} eq =
  ⟦ E >>= F ⟧
    ≡⟨ bind-interpretation F E ⟩ʳ
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ F
    ≡⟨ >>=-ext ⟦ E ⟧ (⟦_⟧ ∘′ F) (⟦_⟧ ∘′ G) eq  ⟩
  ⟦ E ⟧ >>= ⟦_⟧ ∘′ G
    ≡⟨ bind-interpretation G E ⟩
  ⟦ E >>= G ⟧
  ∎
  -}

interchange-interpretation : ∀{A B A′ B′}{{_ : Eq B}}{{_ : Eq B′}}(E : CryptoExpr A B)(F : CryptoExpr A′ B′)(a : A)(a′ : A′)
                           → ⟦ E ***-CE F ⟧ (a , a′) ≡D ⟦ second-CE F >>>-CE first-CE E ⟧ (a , a′)
interchange-interpretation (embed-CE g) F a a′ = lift-D-eq $ cong (λ e → ⟦ e ⟧ (a , a′)) $ embed-interchangeable g F
interchange-interpretation (uniform-CE n E) (embed-CE g) a a′ = lift-D-eq $ {!!} -- follows by similar argument
interchange-interpretation (uniform-CE n E) (uniform-CE m F) a a′ = {!!}

  
