open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.Reindexing {l l′}{T : Set l}{𝑺 : Set l′}(ev : 𝑺 → Set l′)(M : (T → Set l′) → (T → Set l′)){{IMM : IxMonad M}} where

open import Algebra.Lift
open import Algebra.Indexed.Atkey 

open IxMonad IMM

IxStateTᵣ : (𝑺 × T → Set l′) → (𝑺 × T → Set l′)
IxStateTᵣ A (S , t) = ev S → M (λ t′ → Σ 𝑺 λ S′ → A (S′ , t′) × ev S′) t

modify-STᵣ : ∀{S S′ t} → (ev S → ev S′) → IxStateTᵣ (Atkey (ev S′) (S′ , t)) (S , t)
modify-STᵣ {S} {S′} {t} f s = returnⁱ (S′ , V (f s) , f s) 

fmapⁱ-STᵣ : ∀{S A B} → (∀{S′} → A S′ → B S′) → IxStateTᵣ A S → IxStateTᵣ B S
fmapⁱ-STᵣ {S , t} f st s = fmapⁱ (second (first f)) (st s)

lift-STᵣ : ∀{S t A} → M A t → IxStateTᵣ (A ∘′ snd) (S , t)
lift-STᵣ {S} ma s = fmapⁱ (λ a → S , a , s) ma

returnⁱ-STᵣ : ∀{S A} → A S → IxStateTᵣ A S
returnⁱ-STᵣ {S , t} a s = returnⁱ (S , a , s)

bindⁱ-STᵣ : ∀{S A B} → IxStateTᵣ A S → (∀{S′} → A S′ → IxStateTᵣ B S′) → IxStateTᵣ B S
bindⁱ-STᵣ {S , t} {A} {B} st f s = st s >>=ⁱ λ { (S′ , a , s′) → f a s′ }

instance
  IxMonadStateT : IxMonad IxStateTᵣ
  IxMonad.returnⁱ IxMonadStateT {A} {S}     = returnⁱ-STᵣ {S} {A}
  IxMonad._>>=ⁱ_  IxMonadStateT {A} {B} {S} = bindⁱ-STᵣ   {S} {A} {B}
  IxMonad.fmapⁱ   IxMonadStateT {A} {B} {S} = fmapⁱ-STᵣ   {S} {A} {B}
