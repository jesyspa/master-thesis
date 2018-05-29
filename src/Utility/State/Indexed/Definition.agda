module Utility.State.Indexed.Definition {l} where

open import ThesisPrelude
open import Algebra.Lift {lsuc l} {lzero} renaming (Lift to LiftTop; lift to liftTop)
open import Algebra.Lift {lsuc l} {l} renaming (Lift to LiftS; lift to liftS)
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Algebra.Indexed.MonadMorphism
open import Utility.IxIdentity

open import Utility.State.Indexed.Transformer {l′ = l} {T = LiftTop ⊤} (IxIdentity {l}) {{IxMonadIxIdentity}}
open import Algebra.Indexed.Reindexing (λ s → s , LiftTop.lift tt) IxStateT {{IxMonadStateT}}

-- without the reindexing, the type would be 
-- (Set l × Lift ⊤ → Set (lsuc l)) → (Set l × Lift ⊤ → Set (lsuc l))
IxState : (Set l → Set (lsuc l)) → (Set l → Set (lsuc l))
IxState = Reindexed 

open IxMonad {{...}}
open IxMonadMorphism

modify : ∀{S S′} → (S → S′) → IxState (Atkey (LiftS S′) S′) S
modify {S} {S′} f = TermM (ExtractReindexed fst (λ { (a , liftTop tt) → refl })) {_} {S , liftTop tt} lem
  where g : ∀{pr : Set l × LiftTop ⊤}
          → Atkey (LiftS S′) (S′ , liftTop tt) pr
          → Atkey (LiftS S′) S′ (fst pr)
        g {s , liftTop tt} (V r) = V r
        lem : ∀{t} → IxStateT (Atkey (LiftS S′) S′ ∘′ fst) (S , t)
        lem = fmapⁱ {{IxMonadStateT}} {s = S , liftTop tt} g (modifyT {S} {S′} {liftTop tt} f)

instance
  IxMonadState : IxMonad IxState
  IxMonadState = IxMonadReindexed
