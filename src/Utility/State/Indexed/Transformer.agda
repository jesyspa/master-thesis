open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
module Utility.State.Indexed.Transformer {l}{T : Set l}(M : (T → Set l) → (T → Set l)){{IMM : IxMonad M}} where

open import ThesisPrelude

open IxMonad IMM

IxStateT : (Set l × T → Set l) → (Set l × T → Set l)
IxStateT A (S , s) = S → M {!!} {!!}

modify : ∀{S S′ s s′} → (S → S′) → IxStateT {!!} (S , s)
modify = {!!}

{-
fmapⁱ-ST : ∀{S A B} → (∀{S′} → A S′ → B S′) → IxStateT A S → IxStateT B S
fmapⁱ-ST f st s = fmapⁱ (first f) (st s)

returnⁱ-ST : ∀{S A} → A S → IxStateT A S
returnⁱ-ST a s = returnⁱ (a , s)

bindⁱ-ST : ∀{S A B} → IxStateT A S → (∀{S′} → A S′ → IxStateT B S′) → IxStateT B S
bindⁱ-ST st f s = st s >>=ⁱ uncurry f

instance
  IxMonadStateT : IxMonad IxStateT
  IxMonadStateT = record { returnⁱ = returnⁱ-ST ; _>>=ⁱ_ = bindⁱ-ST ; fmapⁱ = fmapⁱ-ST }


-}
