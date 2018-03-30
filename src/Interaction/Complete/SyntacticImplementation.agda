module Interaction.Complete.SyntacticImplementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Implementation 

open ImplMorphism 

SyntacticImplementation : ∀ IS₁ IS₂ → Set
SyntacticImplementation IS₁ IS₂ = Implementation IS₁ (FreeMonad IS₂)

SynImpl = SyntacticImplementation

module _ {IS₁ IS₂} where
  free-SynImpl : ISMorphism IS₁ IS₂ → SynImpl IS₁ IS₂
  free-SynImpl m c = Invoke-FM (CommandF c) (λ r → Return-FM (ResponseF r)) 
    where open ISMorphism m

module _ (M : Set → Set){{_ : Functor M}} {IS₁ IS₂}where
  fmap-Impl : ISMorphism IS₁ IS₂ → ImplMorphism IS₁ M IS₂ M
  UnderlyingISM   (fmap-Impl m) = m
  InterpretationM (fmap-Impl m) mr = fmap ResponseF mr
    where open ISMorphism m

module _ {IS₁ IS₂} where
  fmap-SynImpl-FM : ∀{A} → SynImpl IS₁ IS₂ → FreeMonad IS₁ A → FreeMonad IS₂ A
  fmap-SynImpl-FM si (Return-FM a) = Return-FM a
  fmap-SynImpl-FM si (Invoke-FM c cont) = bind-FM (si c) λ r → fmap-SynImpl-FM si (cont r)

id-SynI : ∀{IS} → SynImpl IS IS 
id-SynI c = Invoke-FM c Return-FM

comp-SynI : ∀{IS₁ IS₂ IS₃} → SynImpl IS₁ IS₂ → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₃ 
comp-SynI si₁ si₂ c = fmap-SynImpl-FM si₂ (si₁ c)

infixr 9 _∘′-SI_
_∘′-SI_ : ∀{IS₁ IS₂ IS₃} → SynImpl IS₂ IS₃ → SynImpl IS₁ IS₂ → SynImpl IS₁ IS₃ 
_∘′-SI_ = flip comp-SynI

module _ {A IS}{ISf : A → InteractionStructure} where
  Match-SynI : (sif : ∀ a → SynImpl (ISf a) IS) → SynImpl (Σ-IS ISf) IS
  Match-SynI = Match-Impl (FreeMonad IS)

module _ {IS₁ IS₂ IS₃} where
  BinMatch-SynI : SynImpl IS₁ IS₃ → SynImpl IS₂ IS₃ → SynImpl (IS₁ ⊎-IS IS₂) IS₃
  BinMatch-SynI = BinMatch-Impl (FreeMonad IS₃)

module _ {A}{ISf₁ ISf₂ : A → InteractionStructure} where
  Join-SynI : (∀ a → SynImpl (ISf₁ a) (ISf₂ a)) → SynImpl (Σ-IS ISf₁) (Σ-IS ISf₂)
  Join-SynI sif (a , c) = fmap-IS-FM (Incl-IS ISf₂ a) (sif a c)

module _ {ISA₁ ISB₁ ISA₂ ISB₂} where
  BinJoin-SynI : SynImpl ISA₁ ISA₂ → SynImpl ISB₁ ISB₂ → SynImpl (ISA₁ ⊎-IS ISB₁) (ISA₂ ⊎-IS ISB₂)
  BinJoin-SynI si₁ si₂ = Join-SynI λ { false → si₁ ; true → si₂ }

module _ {ISA ISB ISBs} where
  Weaken-SynI : ∀{ISB′} → SynImpl ISA (Extend*-IS ISB ISBs) → SynImpl ISA (Extend*-IS ISB (ISB′ ∷ ISBs))
  Weaken-SynI I = comp-SynI I (BinJoin-SynI id-SynI (free-SynImpl (InclR-IS _ _)))
