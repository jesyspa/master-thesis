module Utility.State.Normal {l} where

open import ThesisPrelude
open import Algebra.Lift

module _ (S : Set l) where
  StateT : (Set l → Set l) → Set l → Set l
  StateT M A = S → M (A × S)

module _ {S : Set l}{M : Set l → Set l}{{_ : Monad M}} where
  setT : S → StateT S M (Lift ⊤)
  setT s s′ = return $ lift tt , s

  modifyT : (S → S) → StateT S M S
  modifyT f s = return $ s′ , s′
    where s′ = f s

  getT : StateT S M S
  getT = modifyT id 

  liftT : ∀{A} → M A → StateT S M A
  liftT m s = fmap (λ a → a , s) m
