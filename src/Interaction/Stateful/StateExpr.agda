module Interaction.Stateful.StateExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Algebra.Indexed.LiftMonad
open import Distribution.Class
open import Utility.Vector
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 
open import Interaction.Stateful.Implementation 

open InteractionStructure
open ISMorphism

data StateExprState : Set where
  bitvec-SE  : Nat → StateExprState
  product-SE : StateExprState → StateExprState → StateExprState

eval-SE : StateExprState → Set
eval-SE (bitvec-SE n) = BitVec n
eval-SE (product-SE lhs rhs) = eval-SE lhs × eval-SE rhs

data StateExprCommand (S : StateExprState) : Set where
  modify-SE : ∀ S′ → (eval-SE S → eval-SE S′) → StateExprCommand S

StateExprIS : InteractionStructure
State    StateExprIS = StateExprState
Command  StateExprIS = StateExprCommand
Response StateExprIS (modify-SE S′ _) = eval-SE S′
next     StateExprIS {S} {modify-SE S′ _} r = S′

joinable-CE-IS : ISMorphism (StateExprIS ⊕-IS StateExprIS) StateExprIS
StateF    joinable-CE-IS (s₁ , s₂) = product-SE s₁ s₂
CommandF  joinable-CE-IS {s₁ , s₂} (left  (modify-SE s₁′ f)) = modify-SE (product-SE s₁′ s₂) (first  f)
CommandF  joinable-CE-IS {s₁ , s₂} (right (modify-SE s₂′ f)) = modify-SE (product-SE s₁ s₂′) (second f)
ResponseF joinable-CE-IS {s₁ , s₂} {left  (modify-SE s₁′ f)} r = fst r
ResponseF joinable-CE-IS {s₁ , s₂} {right (modify-SE s₂′ f)} r = snd r
nextF     joinable-CE-IS {s₁ , s₂} {left  (modify-SE s₁′ f)} r = refl
nextF     joinable-CE-IS {s₁ , s₂} {right (modify-SE s₁′ f)} r = refl

{-
module _  where
  open Implementation
  implementation-SE-IS : Implementation StateExprIS {!!}
  StateI  implementation-SE-IS = {!!}
  ImplI   implementation-SE-IS = {!!}

-}
