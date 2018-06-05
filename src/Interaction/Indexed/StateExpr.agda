module Interaction.Indexed.StateExpr where

open import ThesisPrelude
open import Algebra.Lift
open import Algebra.Indexed.Monad
open import Algebra.Indexed.LiftMonad
open import Algebra.Indexed.Atkey
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

data StateExprState : Set where
  bitvec-SE  : Nat → StateExprState
  product-SE : StateExprState → StateExprState → StateExprState

eval-SE : StateExprState → Set
eval-SE (bitvec-SE n) = BitVec n
eval-SE (product-SE lhs rhs) = eval-SE lhs × eval-SE rhs

data StateExprCommand (S : StateExprState) : Set where
  modify-SE : ∀ S′ → (eval-SE S → eval-SE S′) → StateExprCommand S

StateExprIS : InteractionStructure (Leaf StateExprState)
Command  StateExprIS (leaf S) = StateExprCommand S
Response StateExprIS {leaf S} (modify-SE S′ _) = eval-SE S′
next     StateExprIS {leaf S} (modify-SE S′ _) r = leaf S′

joinable-SE-IS : Joinable StateExprIS
StateJ    joinable-SE-IS (leaf s₁) (leaf s₂) = leaf (product-SE s₁ s₂)
CommandF  (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} (left  (modify-SE s₁′ f)) = modify-SE (product-SE s₁′ s₂) (first  f)
CommandF  (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} (right (modify-SE s₂′ f)) = modify-SE (product-SE s₁ s₂′) (second f)
ResponseF (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} {left  (modify-SE s₁′ f)} r = fst r
ResponseF (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} {right (modify-SE s₂′ f)} r = snd r
nextF     (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} {left  (modify-SE s₁′ f)} r = refl
nextF     (IStructJ joinable-SE-IS) {leaf s₁ ▵ leaf s₂} {right (modify-SE s₁′ f)} r = refl

module _ {S}{T : Set}{IS : IStruct S}{M : (T → Set) → (T → Set)}{f : BTAll′ S → T}(Impl : Implementation IS M f){{IMM : IxMonad M}} where
  open import Utility.State.Indexed.FromUniverseTransformer eval-SE M
  open IxMonad {{...}}
  open Implementation

  stateF : BTAll′ (Leaf StateExprState △ S) → StateExprState × T
  stateF = foldsplit-BT′ getleaf-BT′ f
  implementation-SE-IS : Implementation (StateExprIS ⊕-IS IS) IxStateT stateF 
  RunImpl implementation-SE-IS {leaf s₁ ▵ s₂} (left (modify-SE s₁′ g)) = fmapⁱ {s = s₁ , f s₂} rewrap (modifyT g)
    where rewrap : ∀{s′ : StateExprState × T}
                 → Atkey (eval-SE s₁′) (s₁′ , f s₂) s′
                 → StrongAtkey (eval-SE s₁′) (stateF ∘′ next (StateExprIS ⊕-IS IS) {leaf s₁ ▵ s₂} (left (modify-SE s₁′ g))) s′
          rewrap (V s) = StrongV s refl
  RunImpl implementation-SE-IS {leaf s₁ ▵ s₂} (right c) = map-liftT s₁ lem (RunImpl Impl c)
    where
      lem : ∀{t′}
          → StrongAtkey (Response IS c) (f ∘′ next IS c) t′
          → StrongAtkey (Response IS c) (stateF ∘′ next (StateExprIS ⊕-IS IS) {leaf s₁ ▵ s₂} (right c)) (s₁ , t′)
      lem (StrongV r refl) = StrongV r refl
