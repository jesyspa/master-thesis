module Interaction.Stateful.CryptoExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Algebra.Indexed.LiftMonad
open import Algebra.Indexed.Atkey
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
StateF    joinable-CE-IS (tt , tt) = tt
CommandF  joinable-CE-IS {tt , tt} (left  c) = c
CommandF  joinable-CE-IS {tt , tt} (right c) = c
ResponseF joinable-CE-IS {tt , tt} {left  c} r = r
ResponseF joinable-CE-IS {tt , tt} {right c} r = r
nextF     joinable-CE-IS {tt , tt} {left  c} r = refl
nextF     joinable-CE-IS {tt , tt} {right c} r = refl

module _ {l}{S : Set l}(M : Set → Set)(s : S){{DMM : DistMonad M}} where
  open Implementation
  open DistMonad DMM
  implementation-CE-IS : Implementation CryptoExprIS (LiftM M)
  StateI  implementation-CE-IS  tt = s
  ImplI   implementation-CE-IS {tt} (uniform-CE n) = fmap DepV (uniform n)

