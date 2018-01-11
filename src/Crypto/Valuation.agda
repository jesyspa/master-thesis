open import Distribution.Class using (DistMonad)
module Crypto.Valuation (M : Set → Set) {{DM : DistMonad M}} where

open import ThesisPrelude
open import Carrier.Class
open import Distribution.Class
open DistMonad {{...}}
open import Crypto.Syntax

⟦_⟧ : {A : Set} → CryptoExpr A → M A
⟦ returnCE x ⟧ = return x
⟦_⟧ (uniformCE n f) = uniform n >>= λ xs → ⟦ f xs ⟧

