module Crypto.Valuation where

open import ThesisPrelude
open import Carrier.Class
open import Distribution.Class
open import Crypto.Syntax

⟦_⟧ : {A : Set} {M : Set → Set} {{DM : DistMonad M}}
    → CryptoExpr A
    → M A
⟦ returnCE x ⟧ = return x
⟦_⟧ (uniformCE n f) = uniform n >>= λ xs → ⟦ f xs ⟧

eval_as_ : {A : Set} → CryptoExpr A → (M : Set → Set) → {{DM : DistMonad M}}
         → M A
eval e as _ = ⟦ e ⟧
