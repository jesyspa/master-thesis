module Interaction.Indexed.DistExpr where

open import ThesisPrelude
open import Algebra.Proposition
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

data DistExprCommand : Set where
  uniform-DE : Nat → DistExprCommand

DistExprIS : InteractionStructure ⊤
Command  DistExprIS tt = DistExprCommand
Response DistExprIS (uniform-DE n) = BitVec n
next     DistExprIS _ = tt

joinable-DE-IS : Joinable DistExprIS
StateJ              joinable-DE-IS   tt   tt = tt
CommandF  (IStructJ joinable-DE-IS) {tt , tt} (left  c) = c
CommandF  (IStructJ joinable-DE-IS) {tt , tt} (right c) = c
ResponseF (IStructJ joinable-DE-IS) {tt , tt} {left  c} r = r
ResponseF (IStructJ joinable-DE-IS) {tt , tt} {right c} r = r
nextF     (IStructJ joinable-DE-IS) {tt , tt} {left  c} r = refl
nextF     (IStructJ joinable-DE-IS) {tt , tt} {right c} r = refl

module _ (M : Set → Set){{DMM : DistMonad M}} where
  open import Algebra.Indexed.LiftMonad {S = ⊤} M
  open DistMonad DMM
  implementation-DE-IS : Implementation DistExprIS LiftM (const tt)
  RunImpl implementation-DE-IS {tt} (uniform-DE n) = fmap (λ v → StrongV v refl) (uniform n)
