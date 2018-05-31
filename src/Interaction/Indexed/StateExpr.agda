module Interaction.Indexed.StateExpr where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.FunExt
open import Algebra.Indexed.Monad
open import Algebra.Indexed.LiftMonad
open import Algebra.Indexed.Atkey
open import Distribution.Class
open import Utility.Vector
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Interaction.Indexed.Implementation 
open import Interaction.Indexed.Joinable 

open InteractionStructure
open ISMorphism
open Joinable

data StateExprState : Set where
  bitvec-SE  : Nat → StateExprState
  product-SE : StateExprState → StateExprState → StateExprState

eval-SE : StateExprState → Set
eval-SE (bitvec-SE n) = BitVec n
eval-SE (product-SE lhs rhs) = eval-SE lhs × eval-SE rhs

data StateExprCommand (S : StateExprState) : Set where
  modify-SE : ∀ S′ → (eval-SE S → eval-SE S′) → StateExprCommand S

StateExprIS : InteractionStructure StateExprState
Command  StateExprIS = StateExprCommand
Response StateExprIS (modify-SE S′ _) = eval-SE S′
next     StateExprIS {S} {modify-SE S′ _} r = S′

joinable-SE-IS : Joinable StateExprIS
StateJ    joinable-SE-IS = product-SE
CommandF  (IStructJ joinable-SE-IS) {s₁ , s₂} (left  (modify-SE s₁′ f)) = modify-SE (product-SE s₁′ s₂) (first  f)
CommandF  (IStructJ joinable-SE-IS) {s₁ , s₂} (right (modify-SE s₂′ f)) = modify-SE (product-SE s₁ s₂′) (second f)
ResponseF (IStructJ joinable-SE-IS) {s₁ , s₂} {left  (modify-SE s₁′ f)} r = fst r
ResponseF (IStructJ joinable-SE-IS) {s₁ , s₂} {right (modify-SE s₂′ f)} r = snd r
nextF     (IStructJ joinable-SE-IS) {s₁ , s₂} {left  (modify-SE s₁′ f)} r = refl
nextF     (IStructJ joinable-SE-IS) {s₁ , s₂} {right (modify-SE s₁′ f)} r = refl

module _ {S T : Set}{IS : IStruct S}{M : (T → Set) → (T → Set)}{f : S → T}(Impl : Implementation IS M f){{IMM : IxMonad M}} where
  open import Utility.State.Indexed.Reindexing eval-SE M
  open IxMonad {{...}}
  postulate
    implementation-SE-IS : Implementation (StateExprIS ⊕-IS IS) IxStateTᵣ (second f)
  {- this is pretty old
  StateI implementation-SE-IS (s , t) = s , StateI Impl t 
  ImplI  implementation-SE-IS {s , t} (left (modify-SE s′ f)) = fmapⁱ-STᵣ DepV (modify-STᵣ f) 
  -- This looks correct to me, but I still get a lot of yellow.
  ImplI  implementation-SE-IS {s , t} (right c) = fmapⁱ fun goal
    where goal : IxStateTᵣ (DepAtkey (Response IS c) (StateI Impl ∘′ next IS) ∘′ snd) (s , StateI Impl t)
          goal = lift-STᵣ (ImplI Impl c)
          fun : ∀{S′} → DepAtkey (Response IS c) (StateI Impl ∘′ next IS) (snd S′)
              → DepAtkey (Response IS c) (StateI implementation-SE-IS ∘′ next (StateExprIS ⊕-IS IS)) S′
          fun {s′ , t′} (DepV x) = DepV x
  -}

