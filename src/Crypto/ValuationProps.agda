import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.ValuationProps (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

open import ThesisPrelude hiding (_>>=_; _<*>_; pure)
open import Crypto.Syntax
open import Crypto.Valuation F
open import Probability.Class
open import Utility.Vector
open import Utility.Bool
open import Algebra.FunctorProps F
open import Algebra.ApplicativeProps F
open import Algebra.MonadProps F
open import Distribution.Class
open import Distribution.PropsClass F
open import Crypto.Props

open DistMonad DMF
open DistMonadProps DMPF 
open MonadProps is-monad
open Monad monad-super
open Applicative (super monad-super)
open ApplicativeProps aprops
open FunctorProps fprops
open Probability probability-super

uniform-dist-interpretation : ∀ n → uniform n ≡ fmap fst (⟦ uniform-expr {⊤} n ⟧ tt)
uniform-dist-interpretation n =
  uniform n
    ≡⟨ fmap-id (uniform n) ⟩
  fmap id (uniform n)
    ≡⟨ fmap-comp fst (λ xs → (xs , tt)) (uniform n) ⟩
  fmap fst (fmap (λ xs → (xs , tt)) (uniform n))
    ≡⟨ cong (fmap fst) (return-simplify (λ xs → (xs , tt)) (uniform n)) ⟩
  fmap fst (uniform n >>= λ xs → return (xs , tt))
  ∎

fmap-interpretation : ∀{A B B′} (f : B → B′)(E : CryptoExpr A B)(a : A)
                    → fmap f (⟦ E ⟧ a) ≡ ⟦ fmap f E ⟧ a
fmap-interpretation f (embed-CE g) a = sym (fmap-of-pure f (g a))
fmap-interpretation f (uniform-CE n ce) a =
  fmap f (uniform n >>= λ xs → ⟦ ce ⟧ (xs , a))
    ≡⟨ fmap-bind f (uniform n) (λ xs → ⟦ ce ⟧ (xs , a)) ⟩
  uniform n >>= (λ xs → fmap f (⟦ ce ⟧ (xs , a)))
    ≡⟨ >>=-ext (uniform n) (λ xs → fmap f (⟦ ce ⟧ (xs , a)))
                           (λ xs → ⟦ fmap-CE f ce ⟧ (xs , a))
                           (λ xs → fmap-interpretation f ce (xs , a)) ⟩
  uniform n >>= (λ xs → ⟦ fmap-CE f ce ⟧ (xs , a))
  ∎

{-
coin-interpretation : coin ≡ fmap fst (⟦ coin-expr {⊤} ⟧ tt)
coin-interpretation rewrite sym (uniform-dist-interpretation 1) = {!!}
-}
