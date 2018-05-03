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

{-
joinable-CE-IS : ISMorphism (CryptoExprIS ⊕-IS CryptoExprIS) CryptoExprIS
StateF    joinable-CE-IS  tt   false        = tt
StateF    joinable-CE-IS  tt   true         = tt
CommandF  joinable-CE-IS {tt} (false , c)   = c
CommandF  joinable-CE-IS {tt} (true  , c)   = c
ResponseF joinable-CE-IS {tt} {false , c} r = r
ResponseF joinable-CE-IS {tt} {true  , c} r = r
nextF     joinable-CE-IS {tt} {_     , c} r = dep-fun-ext _ _ λ { false → refl ; true → refl }

module _ {S : Set}(M : Set → Set){{DMM : DistMonad M}} where
  open Implementation
  open DistMonad DMM
  implementation-CE-IS : Implementation CryptoExprIS {S} (LiftM M)
  StateI  implementation-CE-IS _ = tt
  ImplI   implementation-CE-IS (uniform-CE n) = fmap (λ v → MagicV v refl) (uniform n) 
  -}
