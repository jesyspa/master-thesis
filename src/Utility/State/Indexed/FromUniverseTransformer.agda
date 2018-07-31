open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.FromUniverseTransformer {T U : Set}(ev : U → Set)(M : (T → Set) → (T → Set)){{IMM : IxMonad M}} where

open import Algebra.Indexed.Atkey 

open IxMonad IMM

IxStateT : (U × T → Set) → (U × T → Set)
IxStateT A (u , t) = ev u → M (λ t′ → Σ U λ u′ → A (u′ , t′) × ev u′) t

modifyT : ∀{u u′ t} → (ev u → ev u′) → IxStateT (Atkey (ev u′) (u′ , t)) (u , t)
modifyT {u} {u′} {t} f s = returnⁱ (u′ , V (f s) , f s) 

getT : ∀{u t} → IxStateT (Atkey (ev u) (u , t)) (u , t)
getT = modifyT id

setT : ∀{u u′ t} → ev u′ → IxStateT (Atkey (ev u′) (u′ , t)) (u , t)
setT s = modifyT (const s)

map-liftT : ∀{A B t} u → (∀{t′} → A t′ → B (u , t′)) → M A t → IxStateT B (u , t)
map-liftT u f m s = fmapⁱ (λ a → u , f a , s) m

liftT : ∀{A t} u → M A t → IxStateT (A ∘′ snd) (u , t)
liftT u = map-liftT u id

fmapⁱ-ST : ∀{u A B} → (∀{u′} → A u′ → B u′) → IxStateT A u → IxStateT B u
fmapⁱ-ST {u , t} f st v = fmapⁱ (second (first f)) (st v)

returnⁱ-ST : ∀{u A} → A u → IxStateT A u
returnⁱ-ST {u , t} a s = returnⁱ (u , a , s)

bindⁱ-ST : ∀{u A B} → IxStateT A u → (∀{u′} → A u′ → IxStateT B u′) → IxStateT B u
bindⁱ-ST {u , t} st f s = st s >>=ⁱ λ { (u′ , a , s′) → f a s′ }

instance
  IxMonadStateT : IxMonad IxStateT
  IxMonad.returnⁱ IxMonadStateT {A} {u}     = returnⁱ-ST {u} {A}
  IxMonad._>>=ⁱ_  IxMonadStateT {A} {B} {u} = bindⁱ-ST   {u} {A} {B}
  IxMonad.fmapⁱ   IxMonadStateT {A} {B} {u} = fmapⁱ-ST   {u} {A} {B}
