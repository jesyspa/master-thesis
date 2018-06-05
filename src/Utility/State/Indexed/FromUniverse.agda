open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.FromUniverse {U : Set}(ev : U → Set) where

open import Utility.Identity
open import Algebra.Indexed.LiftMonad
open import Utility.State.Indexed.FromUniverseTransformer ev (LiftM {S = ⊤} Identity) {{IxMonadLiftM Identity}}
open import Algebra.Indexed.Atkey 
open import Algebra.Indexed.MonadMorphism 
open import Algebra.Indexed.Reindexing {T = U} (λ u → u , tt) IxStateT {{it}}

open IxMonad {{...}}
open IxMonadMorphism 

IxState : (U → Set) → (U → Set)
IxState = Reindexed 

modify : ∀{u u′} → (ev u → ev u′) → IxState (Atkey (ev u′) u′) u
modify {u} {u′} f s = u′ , (u′ , refl , V (f s)) , f s

instance
  IxMonadState : IxMonad IxState
  IxMonadState = IxMonadReindexed
