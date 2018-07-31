open import ThesisPrelude using (Monad)
open import Algebra.Parametrised.Monad 
module Utility.State.Parametrised.Transformer {l l′}{T : Set l′}(M : T → T → Set l → Set l){{PMM : ParMonad T M}} where

open import ThesisPrelude

open ParMonad PMM

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

bindᵖ-ST : ∀{S S′ S″ A B} → ParStateT S S′ A → (A → ParStateT S′ S″ B) → ParStateT S S″ B
bindᵖ-ST {_ , _} {_ , _} {_ , _} st f = λ s → st s >>=ᵖ uncurry f

instance
  -- I have no clue why the explicit annotations are necessary here.
  ParMonadStateT : ParMonad (T × Set l) ParStateT
  ParMonad.returnᵖ       ParMonadStateT {S} a = returnᵖ-ST {S} a
  ParMonad._>>=ᵖ_        ParMonadStateT {S₀} {S₁} {S₂} st f = bindᵖ-ST {S₀} {S₁} {S₂} st f
  ParMonad.super-functor ParMonadStateT {S} {S′} = FunctorStateT {S} {S′}

modifyᵖ-ST : ∀{S S′ t} → (S → S′) → ParStateT (t , S) (t , S′) S′
modifyᵖ-ST f = λ s → returnᵖ (f s , f s)

