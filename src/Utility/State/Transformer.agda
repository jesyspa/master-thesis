open import ThesisPrelude
module Utility.State.Transformer {l}(M : Set l → Set l){{_ : Monad M}} where

StateT : Set l → Set l → Set l → Set l
StateT S S′ X = S → M (X × S′)

fmap-ST : ∀{S S′ X Y} → (X → Y) → StateT S S′ X → StateT S S′ Y
fmap-ST f st = λ s → fmap (first f) (st s)

instance
  FunctorStateT : ∀{S S′} → Functor (StateT S S′)
  FunctorStateT = record { fmap = fmap-ST }
