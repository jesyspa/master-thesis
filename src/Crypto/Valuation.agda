open import Distribution.Class using (DistMonad)
module Crypto.Valuation (M : Set → Set) {{DM : DistMonad M}} where

open import ThesisPrelude
open import Probability.Class
open import Distribution.Class
open DistMonad {{...}}
open import Crypto.Syntax

⟦_⟧ : {A B : Set} → CryptoExpr A B → A → M B 
⟦ embed-CE g ⟧ a = pure (g a)
⟦ uniform-CE n ce ⟧ a = uniform n >>= λ xs → ⟦ ce ⟧ (xs , a)

