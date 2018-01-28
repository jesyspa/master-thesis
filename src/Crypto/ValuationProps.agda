import Distribution.Class as DC
import Distribution.PropsClass as DPC
module Crypto.ValuationProps (F : Set → Set) {{DMF : DC.DistMonad F}} {{DMPF : DPC.DistMonadProps F}} where

open import ThesisPrelude hiding (_>>=_; _<*>_; pure)
open import Crypto.Syntax
open import Crypto.Valuation F
open import Probability.Class
open import Utility.Vector
open import Utility.Product
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

-- Is there a more useful way to phrase these properties?
embed-interpretation : ∀{A B}(f : A → B)(a : A)
                     → return (f a) ≡ ⟦ embed-CE f ⟧ a
embed-interpretation f a = refl

uniform-interpretation : ∀{A B} n (ce : CryptoExpr (BitVec n × A) B)(a : A)
                       → (uniform n >>= λ xs → ⟦ ce ⟧ (xs , a)) ≡ ⟦ uniform-CE n ce ⟧ a
uniform-interpretation n ce a = refl

uniform-dist-interpretation : ∀{A} n (a : A) → (uniform n >>= λ xs → return (xs , a)) ≡ ⟦ uniform-expr n ⟧ a
uniform-dist-interpretation n a = refl

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

cofmap-interpretation : ∀{A A′ B} (f : A → A′)(E : CryptoExpr A′ B)(a : A)
                      → ⟦ E ⟧ (f a) ≡ ⟦ cofmap-CE f E ⟧ a
cofmap-interpretation f (embed-CE g) a = refl
cofmap-interpretation f (uniform-CE n E) a =
  (uniform n >>= λ xs → ⟦ E ⟧ (xs , f a))
    ≡⟨ >>=-ext (uniform n) (λ xs → ⟦ E ⟧ (xs , f a))
                           (λ xs → ⟦ cofmap-CE (second f) E ⟧ (xs , a))
                           (λ xs → cofmap-interpretation (second f) E (xs , a) ) ⟩
  (uniform n >>= λ xs → ⟦ cofmap-CE (second f) E ⟧ (xs , a))
  ∎


comp-interpretation : ∀{A B C}(lhs : CryptoExpr A B)(rhs : CryptoExpr B C)(a : A)
                    → (⟦ lhs ⟧ a >>= ⟦ rhs ⟧) ≡ ⟦ lhs >>>-CE rhs ⟧ a
comp-interpretation (embed-CE g) rhs a =
  return (g a) >>= ⟦ rhs ⟧
    ≡⟨ return->>=-left-id (g a) ⟦ rhs ⟧ ⟩
  ⟦ rhs ⟧ (g a)
    ≡⟨ cofmap-interpretation g rhs a ⟩
  ⟦ cofmap-CE g rhs ⟧ a
  ∎
comp-interpretation (uniform-CE n lhs) rhs a =
  uniform n >>= (λ xs → ⟦ lhs ⟧ (xs , a)) >>= ⟦ rhs ⟧
    ≡⟨ >>=-assoc (uniform n) (λ xs → ⟦ lhs ⟧ (xs , a)) ⟦ rhs ⟧ ⟩
  uniform n >>= (λ xs → ⟦ lhs ⟧ (xs , a) >>= ⟦ rhs ⟧)
    ≡⟨ >>=-ext (uniform n) (λ xs → ⟦ lhs ⟧ (xs , a) >>= ⟦ rhs ⟧)
                           (λ xs → ⟦ lhs >>>-CE rhs ⟧ (xs , a))
                           (λ xs → comp-interpretation lhs rhs (xs , a)) ⟩
  uniform n >>= (λ xs → ⟦ lhs >>>-CE rhs ⟧ (xs , a))
  ∎

first-interpretation : ∀{A B C}(ce : CryptoExpr A B)(a : A)(c : C)
                     → (⟦ ce ⟧ a >>= λ b → return (b , c)) ≡ ⟦ first-CE ce ⟧ (a , c)
first-interpretation (embed-CE g) a c =
  return (g a) >>= (λ b → return (b , c))
    ≡⟨ return->>=-left-id (g a) (λ b → return (b , c)) ⟩
  return (first g (a , c))
  ∎
first-interpretation (uniform-CE n ce) a c =
  uniform n >>= (λ xs → ⟦ ce ⟧ (xs , a)) >>= (λ b → return (b , c))
    ≡⟨ >>=-assoc (uniform n) (λ xs → ⟦ ce ⟧ (xs , a)) (λ b → return (b , c)) ⟩
  uniform n >>= (λ xs → ⟦ ce ⟧ (xs , a) >>= λ b → return (b , c))
    ≡⟨ >>=-ext (uniform n) (λ xs → ⟦ ce ⟧ (xs , a) >>= λ b → return (b , c))
                           (λ xs → ⟦ cofmap-CE unassoc (first-CE ce) ⟧ (xs , a , c))
                           (λ xs →
                             ⟦ ce ⟧ (xs , a) >>= (λ b → return (b , c))
                               ≡⟨ first-interpretation ce (xs , a) c ⟩
                             ⟦ first-CE ce ⟧ ((xs , a) , c)
                               ≡⟨ cofmap-interpretation unassoc (first-CE ce) (xs , a , c) ⟩
                             ⟦ cofmap-CE unassoc (first-CE ce) ⟧ (xs , a , c)
                             ∎
                             )⟩
  uniform n >>= (λ xs → ⟦ cofmap-CE unassoc (first-CE ce) ⟧ (xs , a , c))
  ∎
