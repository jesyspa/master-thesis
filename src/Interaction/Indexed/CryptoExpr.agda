module Interaction.Indexed.CryptoExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Algebra.Lift
open import Algebra.Indexed.LiftMonad
open import Algebra.Indexed.Atkey
open import Algebra.Unit
open import Distribution.Class
open import Utility.Vector
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Interaction.Indexed.Implementation 
open import Interaction.Indexed.Joinable 

open InteractionStructure
open ISMorphism
open Joinable
open Implementation

data CryptoExprCommand : Set where
  uniform-CE : Nat → CryptoExprCommand

CryptoExprIS : InteractionStructure ⊤
Command  CryptoExprIS tt = CryptoExprCommand
Response CryptoExprIS (uniform-CE n) = BitVec n
next     CryptoExprIS _ = tt

joinable-CE-IS : Joinable CryptoExprIS
StateJ              joinable-CE-IS   tt   tt = tt
CommandF  (IStructJ joinable-CE-IS) {tt , tt} (left  c) = c
CommandF  (IStructJ joinable-CE-IS) {tt , tt} (right c) = c
ResponseF (IStructJ joinable-CE-IS) {tt , tt} {left  c} r = r
ResponseF (IStructJ joinable-CE-IS) {tt , tt} {right c} r = r
nextF     (IStructJ joinable-CE-IS) {tt , tt} {left  c} r = refl
nextF     (IStructJ joinable-CE-IS) {tt , tt} {right c} r = refl

module _ (M : Set → Set){{DMM : DistMonad M}} where
  open DistMonad DMM
  implementation-CE-IS : Implementation CryptoExprIS (LiftM M {S = ⊤}) (const tt)
  RunImpl implementation-CE-IS {tt} (uniform-CE n) = fmap (λ v → lift $ StrongV v refl) (uniform n)

