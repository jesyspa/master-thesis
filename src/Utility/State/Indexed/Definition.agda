module Utility.State.Indexed.Definition {l} where

open import ThesisPrelude
open import Algebra.Lift
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Reindexing
open import Utility.IxIdentity

open import Utility.State.Indexed.Transformer {l′ = l} {T = Lift ⊤} (IxIdentity {l}) {{IxMonadIxIdentity}}

-- without the reindexing, the type would be 
-- (Set l × Lift ⊤ → Set (lsuc l)) → (Set l × Lift ⊤ → Set (lsuc l))
IxState : (Set l → Set (lsuc l)) → (Set l → Set (lsuc l))
IxState = Reindexed (λ s → s , lift tt) IxStateT
