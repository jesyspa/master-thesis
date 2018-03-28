module Interaction.Complete.Player where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 

open InteractionStructure
open ISMorphism

record MethodSig : Set₁ where
  constructor method-sig
  field
    Argument : Set
    Result : Argument → Set
open MethodSig

method-sig′ : Set → Set → MethodSig
method-sig′ arg res = method-sig arg (const res)

record PlayerSig : Set₁ where
  constructor player-sig
  field
    MethodName : Set
    MethodSigs : MethodName → MethodSig
open PlayerSig

Trivial-PS : PlayerSig
MethodName Trivial-PS = ⊥
MethodSigs Trivial-PS ()

module _ {I : Set}(sigs : I → PlayerSig) where
  Union-PS : PlayerSig
  MethodName Union-PS = Σ I (MethodName ∘′ sigs)
  MethodSigs Union-PS (i , name) = MethodSigs (sigs i) name 

module _ (sig₁ sig₂ : PlayerSig) where
  private
    bincase : Bool → PlayerSig
    bincase false = sig₁
    bincase true  = sig₂
  BinUnion-PS : PlayerSig
  BinUnion-PS = Union-PS bincase

BinUnion*-PS : List PlayerSig → PlayerSig
BinUnion*-PS = foldr BinUnion-PS Trivial-PS

module _ (M : Set → Set) where
  MethodImpl : MethodSig → Set
  MethodImpl msig = (arg : Argument msig) → M (Result msig arg)

  PlayerImpl : PlayerSig → Set
  PlayerImpl sig = (name : MethodName sig) → MethodImpl (MethodSigs sig name)

  ImplTrivial-PS : PlayerImpl Trivial-PS
  ImplTrivial-PS ()

  module _ {I : Set}(sigs : I → PlayerSig) where
    ImplUnion-PS : (∀ i → PlayerImpl (sigs i)) → PlayerImpl (Union-PS sigs)
    ImplUnion-PS fn (i , name) = fn i name

module _ (M₁ M₂ : Set → Set) where
  MIMorphism : Set₁
  MIMorphism = ∀{sig} → MethodImpl M₁ sig → MethodImpl M₂ sig
  
  PIMorphism : Set₁
  PIMorphism = ∀{sig} → PlayerImpl M₁ sig → PlayerImpl M₂ sig
  
  fmap-PI : MIMorphism → PIMorphism
  fmap-PI m plr name = m (plr name)

  FunctorMorphism : Set₁
  FunctorMorphism = ∀{A} → M₁ A → M₂ A

  Reinterpret-PI : FunctorMorphism → {sig : PlayerSig} → PlayerImpl M₁ sig → PlayerImpl M₂ sig
  Reinterpret-PI mrph impl name arg = mrph (impl name arg)

module _ {IS₁ IS₂ : InteractionStructure} where
  fmap-MI : FMMorphism IS₁ IS₂ → MIMorphism (FreeMonad IS₁) (FreeMonad IS₂)
  fmap-MI m impl arg = m (impl arg)
  
Sig2IS : PlayerSig → InteractionStructure
Command  (Sig2IS sig) = Σ (MethodName sig) (Argument ∘′ MethodSigs sig)
Response (Sig2IS sig) (name , arg) = Result (MethodSigs sig name) arg 
  
record PlayerDef : Set₁ where
  constructor player-def
  field
    IS-PD  : InteractionStructure 
    Sig-PD : PlayerSig
open PlayerDef

Trivial-PD : PlayerDef
Trivial-PD = player-def Zero-IS Trivial-PS
      
Impl-PD : PlayerDef → Set
Impl-PD (player-def IS sig) = PlayerImpl (FreeMonad IS) sig

ImplTrivial-PD : Impl-PD Trivial-PD
ImplTrivial-PD = ImplTrivial-PS (FreeMonad Zero-IS)

Join-PD : PlayerDef → PlayerDef → PlayerDef
IS-PD  (Join-PD def₁ def₂) = BinCoproduct-IS (IS-PD def₁) (IS-PD def₂)
Sig-PD (Join-PD def₁ def₂) = BinUnion-PS (Sig-PD def₁) (Sig-PD def₂)

Join*-PD : List PlayerDef → PlayerDef
Join*-PD = foldr Join-PD Trivial-PD

Extend-PD : PlayerDef → PlayerDef → PlayerDef
IS-PD  (Extend-PD def₁ def₂) = BinCoproduct-IS (IS-PD def₁) (Sig2IS (Sig-PD def₂))
Sig-PD (Extend-PD def₁ def₂) = Sig-PD def₁

MkExtend*-PD : List PlayerDef → PlayerDef
MkExtend*-PD = foldr Extend-PD Trivial-PD

Extend*-PD : PlayerDef → List PlayerDef → PlayerDef
Extend*-PD def defs = Extend-PD def (Join*-PD defs)

{- Idea:
Given a list of playersigs, we can get a corresponding list of implementations.
The list of implementations uses playersigs augmented with earlier ISs.
We can combine the implementations using the usual combine construction.
Can we combine interpretations of these implementations the same way?  Should be doable.
-}

