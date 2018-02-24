open import ThesisPrelude using (Monad) 
module Algebra.Parametrised.Lift {l l′}(𝑺 : Set l′)(M : Set l → Set l){{_ : Monad M}} where

open import ThesisPrelude
open import Algebra.Parametrised.Monad

Lifted : 𝑺 → 𝑺 → Set l → Set l
Lifted _ _ = M


instance
  LiftedMonad : ParMonad 𝑺 Lifted 
  LiftedMonad = record { returnᵖ = return ; _>>=ᵖ_ = _>>=_ }

open import Algebra.MonadProps M
open import Algebra.Parametrised.MonadProps 𝑺 Lifted 

module _ {{MP : MonadProps}} where
  open MonadProps MP
  instance
    ParMonadPropsLifted : ParMonadProps
    ParMonadPropsLifted = record
                            { >>=-assocᵖ = >>=-assoc
                            ; return->>=-right-idᵖ = return->>=-right-id
                            ; return->>=-left-idᵖ = return->>=-left-id
                            ; >>=-extᵖ = >>=-ext
                            }
