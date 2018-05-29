open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.Reindexing {l′}{𝑺 : Set l′}(ev : 𝑺 → Set l′) where

open import Algebra.Lift
open import Algebra.Indexed.Atkey 
open import Utility.State.Indexed.Definition 

open import Algebra.Indexed.Reindexing {S = Set l′}{T = 𝑺} ev IxState {{it}}

open IxMonad IxMonadReindexed

IxStateᵣ : (𝑺 → Set (lsuc l′)) → (𝑺 → Set (lsuc l′))
IxStateᵣ = Reindexed 

modifyᵣ : ∀{S S′} → (ev S → ev S′) → IxStateᵣ (Atkey (Lift (ev S′)) S′) S
modifyᵣ {S} {S′} f s = ev S′ , (ev S′ , refl , S′ , refl , V (lift (f s))) , f s

instance
  IxMonadStateᵣ : IxMonad IxStateᵣ
  IxMonadStateᵣ = IxMonadReindexed
