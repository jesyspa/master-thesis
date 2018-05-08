open import ThesisPrelude using (Monad)
open import Algebra.Parametrised.Monad 
module Utility.State.Parametrised.Transformer {l l′}{T : Set l′}(M : T → T → Set l → Set l){{_ : ParMonad T M}} where

open import ThesisPrelude

ParStateT : T × Set l → T × Set l → Set l → Set l
ParStateT (t , S) (t′ , S′) X = S → M t t′ (X × S′)

fmap-ST : ∀{S S′ A B} → (A → B) → ParStateT S S′ A → ParStateT S S′ B
fmap-ST {S , t} {S′ , t′} f st s = fmap (first f) (st s)

module _ {S S′} where
  instance
    FunctorStateT : Functor (ParStateT S S′)
    FunctorStateT = record { fmap = fmap-ST {S} {S′} }

returnᵖ-ST : ∀{S A} → A → ParStateT S S A
returnᵖ-ST {t , S} a = λ s → returnᵖ (a , s)

bindᵖ-ST : ∀{S S′ S′′ A B} → ParStateT S S′ A → (A → ParStateT S′ S′′ B) → ParStateT S S′′ B
bindᵖ-ST {_ , _} {_ , _} {_ , _} st f = λ s → st s >>=ᵖ uncurry f

instance
  ParMonadStateT : ParMonad (T × Set l) ParStateT
  returnᵖ {{ParMonadStateT}} a = returnᵖ-ST a
  _>>=ᵖ_  {{ParMonadStateT}} st f = bindᵖ-ST st f
