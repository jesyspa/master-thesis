module Interaction.Indexed.StateExpr where

open import ThesisPrelude
open import Algebra.Lift
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

module _ {S T : Set}{IS : IStruct S}{M : (T → Set₁) → (T → Set₁)}{f : S → T}(Impl : Implementation IS M f){{IMM : IxMonad M}} where
  open import Utility.State.Indexed.ReindexingTransformer eval-SE M
  open IxMonad {{...}}
  open Implementation

  implementation-SE-IS : Implementation (StateExprIS ⊕-IS IS) IxStateTᵣ (second f)
  RunImpl implementation-SE-IS {s₁ , s₂} (left (modify-SE s₁′ g)) = fmapⁱ {s = s₁ , f s₂} rewrap (modifyTᵣ {s₁} {s₁′} {f s₂} g)
    where rewrap : ∀{s′ : StateExprState × T}
                 → Atkey (Lift (eval-SE s₁′)) (s₁′ , f s₂) s′
                 → Lift (StrongAtkey (eval-SE s₁′) (second f ∘′ next (StateExprIS ⊕-IS IS) {s₁ , s₂} {left (modify-SE s₁′ g)} ) s′)
          rewrap (V (lift s)) = lift (StrongV s refl)
  RunImpl implementation-SE-IS {s₁ , s₂} (right c) = map-liftTᵣ s₁ lem (RunImpl Impl c)
    where
      lem : ∀{t′}
          → Lift (StrongAtkey (Response IS c) (f ∘′ next IS) t′)
          → Lift (StrongAtkey (Response IS c) (second f ∘′ next (StateExprIS ⊕-IS IS) {s₁ , s₂} {right c}) (s₁ , t′))
      lem (lift (StrongV r refl)) = lift $ StrongV r refl
  

