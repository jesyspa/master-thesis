open import ThesisPrelude using (Monad)
open import Algebra.Parametrised.Monad 
module Utility.State.Parametrised.Transformer {l}(M : Set l → Set l → Set l → Set l){{_ : ParMonad (Set l) M}} where

open import ThesisPrelude

ParStateT : Set l → Set l → Set l → Set l
ParStateT S S′ X = S → M S S′ (X × S′)

fmap-ST : ∀{S S′ X Y} → (X → Y) → ParStateT S S′ X → ParStateT S S′ Y
fmap-ST f st = λ s → fmap (first f) (st s)

instance
  FunctorStateT : ∀{S S′} → Functor (ParStateT S S′)
  FunctorStateT = record { fmap = fmap-ST }

preturn-ST : ∀{S X} → X → ParStateT S S X
preturn-ST x = λ s → returnᵖ (x , s)

pbind-ST : ∀{S S′ S′′ X Y} → ParStateT S S′ X → (X → ParStateT S′ S′′ Y) → ParStateT S S′′ Y
pbind-ST st f = λ s → st s >>=ᵖ uncurry f

instance
  ParMonadStateT : ParMonad (Set l) ParStateT
  ParMonadStateT = record { returnᵖ = preturn-ST ; _>>=ᵖ_ = pbind-ST }

