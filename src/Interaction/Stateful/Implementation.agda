module Interaction.Stateful.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 

open InteractionStructure
open IxMonad {{...}}

module _ (IS : InteractionStructure){S : Set} where
  record Implementation (M : (S → Set) → S → Set) : Set where
    field 
      StateI : S → State IS
      ImplI  : {s : S}(c : Command IS (StateI s)) → M (MagicAtkey (Response IS c) StateI (next IS)) s
open Implementation

module _ {IS S}{M : (S → Set) → S → Set}{{_ : IxMonad M}} where
  open IxMonadMorphism
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M → IxMonadMorphism (FreeMonad IS) M
  StateM (uprop-Impl impl) = StateI impl
  TermM (uprop-Impl impl) (Return-FM a) = returnⁱ a
  TermM (uprop-Impl impl) (Invoke-FM c cont) = ImplI impl c >>=ⁱ λ { (MagicV r pf) → TermM (uprop-Impl impl) (transport (FreeMonad IS _) pf (cont r)) }

SyntacticImplementation : (IS₁ IS₂ : InteractionStructure) → Set
SyntacticImplementation IS₁ IS₂ = Implementation IS₁ (FreeMonad IS₂)

SynImpl = SyntacticImplementation

module _ {IS : InteractionStructure} where
  id-SI : SynImpl IS IS
  StateI id-SI = id
  ImplI  id-SI c = Invoke-FM c λ r → Return-FM (MagicV r refl)

module _ {IS₁ IS₂} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂) → IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂) 
  fmap-SynImpl-FM = uprop-Impl

module _ {IS₁ IS₂ IS₃ : InteractionStructure} where
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  StateI (comp-SI si sj) = StateI si ∘′ StateI sj
  ImplI  (comp-SI si sj) {s} c = goal
    where
      -- It's a bit weird to do things this way, but I think that in order to show this directly I would
      -- have to assume univalence, since the result types really are nominally different.
      -- I've written it out explicitly to show the types.
      lem : FreeMonad IS₃ (MagicAtkey (Response IS₁ c) (StateI si) (next IS₁) ∘′ StateI sj) s
      lem = IxMonadMorphism.TermM (fmap-SynImpl-FM sj) (ImplI si c)
      goal : FreeMonad IS₃ (MagicAtkey (Response IS₁ c) (StateI si ∘′ StateI sj) (next IS₁)) s
      goal = lem >>=ⁱ λ { (MagicV r pf) → returnⁱ (MagicV r pf) }

module _ {IS₁ IS₂}(m : ISMorphism IS₁ IS₂) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂
  StateI fmap-IS-SynImpl = StateF 
  ImplI  fmap-IS-SynImpl c = Invoke-FM (CommandF c) λ r → Return-FM (MagicV (ResponseF r) (sym $ nextF r))

  fmap-IS-FM : IxMonadMorphism (FreeMonad IS₁) (FreeMonad IS₂)
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl
