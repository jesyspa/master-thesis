open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.Transformer {l l′}{T : Set l}(M : (T → Set (lsuc l′)) → (T → Set (lsuc l′))){{IMM : IxMonad M}} where

open import Algebra.Lift
open import Algebra.Indexed.Atkey 

open IxMonad IMM

IxStateT : (Set l′ × T → Set (lsuc l′)) → (Set l′ × T → Set (lsuc l′))
IxStateT A (S , t) = S → M (λ t′ → Σ (Set l′) λ S′ → A (S′ , t′) × S′) t

modifyT : ∀{S S′ t} → (S → S′) → IxStateT (Atkey (Lift S′) (S′ , t)) (S , t)
modifyT {S} {S′} {t} f s = returnⁱ (S′ , V (lift (f s)) , f s) 

map-liftT : ∀{A B t} S → (∀{t′} → A t′ → B (S , t′)) → M A t → IxStateT B (S , t)
map-liftT S f m s = fmapⁱ (λ a → S , f a , s) m

liftT : ∀{A t} S → M A t → IxStateT (A ∘′ snd) (S , t)
liftT S = map-liftT S id

fmapⁱ-ST : ∀{S A B} → (∀{S′} → A S′ → B S′) → IxStateT A S → IxStateT B S
fmapⁱ-ST {S , t} f st s = fmapⁱ (second (first f)) (st s)

returnⁱ-ST : ∀{S A} → A S → IxStateT A S
returnⁱ-ST {S , t} a s = returnⁱ (S , a , s)

bindⁱ-ST : ∀{S A B} → IxStateT A S → (∀{S′} → A S′ → IxStateT B S′) → IxStateT B S
bindⁱ-ST {S , t} {A} {B} st f s = st s >>=ⁱ λ { (S′ , a , s′) → f a s′ }

instance
  IxMonadStateT : IxMonad IxStateT
  IxMonad.returnⁱ IxMonadStateT {A} {S}     = returnⁱ-ST {S} {A}
  IxMonad._>>=ⁱ_  IxMonadStateT {A} {B} {S} = bindⁱ-ST   {S} {A} {B}
  IxMonad.fmapⁱ   IxMonadStateT {A} {B} {S} = fmapⁱ-ST   {S} {A} {B}

