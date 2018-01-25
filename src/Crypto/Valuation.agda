open import Distribution.Class using (DistMonad)
module Crypto.Valuation (M : Set → Set) {{DM : DistMonad M}} where

open import ThesisPrelude
open import Utility.List.Elem
open import Probability.Class
open import Distribution.Class
open DistMonad {{...}}
open import Crypto.Syntax

data Interpretation : OracleList → Set where
  empty : Interpretation []
  cons : ∀{O X Y} → (X → Y) → Interpretation O → Interpretation ((X , Y) ∷ O)

lookup-in-Interpretation : ∀{O X Y}(p : (X , Y) ∈ O) → Interpretation O → X → Y
lookup-in-Interpretation (here .(_ , _) xs) (cons f os) = f
lookup-in-Interpretation (there .(_ , _) .(_ , _) xs p) (cons x os) = lookup-in-Interpretation p os

⟦_⟧ : ∀{O O′}{A : Set} → CryptoExpr O O′ A → Interpretation O → M A
⟦ returnCE a ⟧ os = return a
⟦ uniformCE n cont ⟧ os = uniform n >>= λ xs → (⟦ cont xs ⟧ os)
⟦ callOracleCE p x cont ⟧ os = ⟦ cont (lookup-in-Interpretation p os x) ⟧ os
⟦ addOracleCE f ce ⟧ os = ⟦ ce ⟧ (cons f os)

