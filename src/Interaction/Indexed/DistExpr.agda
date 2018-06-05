module Interaction.Indexed.DistExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Indexed.Atkey
open import Algebra.Unit
open import Distribution.Class
open import Utility.Vector
open import Utility.BTAll
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

DistExprIS : InteractionStructure Empty
Command  DistExprIS empty = DistExprCommand
Response DistExprIS {empty} (uniform-DE n) = BitVec n
next     DistExprIS {empty} (uniform-DE n) _ = empty

joinable-DE-IS : Joinable DistExprIS
StateJ              joinable-DE-IS   empty   empty = empty
CommandF  (IStructJ joinable-DE-IS) {empty ▵ empty} (left  c) = c
CommandF  (IStructJ joinable-DE-IS) {empty ▵ empty} (right c) = c
ResponseF (IStructJ joinable-DE-IS) {empty ▵ empty} {left  c} r = r
ResponseF (IStructJ joinable-DE-IS) {empty ▵ empty} {right c} r = r
nextF     (IStructJ joinable-DE-IS) {empty ▵ empty} {left  (uniform-DE n)} r = refl
nextF     (IStructJ joinable-DE-IS) {empty ▵ empty} {right (uniform-DE n)} r = refl

module _ (M : Set → Set){{DMM : DistMonad M}} where
  open import Algebra.Indexed.LiftMonad {S = ⊤} M
  open DistMonad DMM
  implementation-DE-IS : Implementation DistExprIS LiftM (const tt)
  RunImpl implementation-DE-IS {empty} (uniform-DE n) = fmap (λ v → StrongV v refl) (uniform n)
