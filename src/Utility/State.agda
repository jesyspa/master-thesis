module Utility.State where

open import ThesisPrelude

StateT : Set → (Set → Set) → Set → Set
StateT S M A = S → M (S × A)

get : ∀{S M}{{_ : Monad M}} → StateT S M S
get s = return (s , s)

set : ∀{S M}{{_ : Monad M}} → S → StateT S M ⊤
set s _ = return (s , tt)

modify : ∀{S M}{{_ : Monad M}} → (S → S) → StateT S M S
modify f s = return (f s , f s)

lift : ∀{S M A}{{_ : Monad M}} → M A → StateT S M A
lift m s = m >>= λ a → return (s , a)
