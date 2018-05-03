module Interaction.Stateful.CryptoExpr where

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

data CryptoExprCommand : Set where
  uniform-CE : Nat → CryptoExprCommand

CryptoExprIS : InteractionStructure
State    CryptoExprIS = ⊤
Command  CryptoExprIS tt = CryptoExprCommand
Response CryptoExprIS (uniform-CE n) = BitVec n
next     CryptoExprIS _ = tt

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
