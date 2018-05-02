module Interaction.Stateful.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Stateful.InteractionStructure 
open import Interaction.Stateful.FreeMonad 

open InteractionStructure

module _ (IS : InteractionStructure){S : Set} where
  record Implementation (M : (S → Set) → S → Set) : Set where
    field 
      StateI : S → State IS
      ImplI  : {s : S}(c : Command IS (StateI s)) → M (MagicAtkey (Response IS c) StateI (next IS)) s
open Implementation

SyntacticImplementation : (IS₁ IS₂ : InteractionStructure) → Set
SyntacticImplementation IS₁ IS₂ = Implementation IS₁ (FreeMonad IS₂)

SynImpl = SyntacticImplementation

module _ {IS : InteractionStructure} where
  id-SI : SynImpl IS IS
  StateI id-SI = id
  ImplI  id-SI c = Invoke-FM c λ r → Return-FM (MagicV r refl)

module _ {IS₁ IS₂} where
  {-# TERMINATING #-}
  fmap-SynImpl-FM : ∀{s A} → (si : SynImpl IS₁ IS₂) → FreeMonad IS₁ A (StateI si s) → FreeMonad IS₂ (A ∘′ StateI si) s
  fmap-SynImpl-FM si (Return-FM a) = Return-FM a
  fmap-SynImpl-FM {A = A} si (Invoke-FM c cont) = bind-FM (ImplI si c) λ { (MagicV r pf) → fmap-SynImpl-FM si (transport (FreeMonad IS₁ A) pf (cont r)) }

module _ {IS₁ IS₂ IS₃ : InteractionStructure} where
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃
  StateI (comp-SI si sj) = StateI si ∘′ StateI sj
  ImplI  (comp-SI si sj) {s} c = bind-FM lem λ { (MagicV r pf) → Return-FM (MagicV r pf) }
    where
      lem : FreeMonad IS₃ (MagicAtkey (Response IS₁ c) (StateI si) (next IS₁) ∘′ StateI sj) s
      lem = fmap-SynImpl-FM sj (ImplI si c)
