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

module _ (IS : InteractionStructure) where
  MethodImpl : MethodSig → Set
  MethodImpl msig = (arg : Argument msig) → FreeMonad IS (Result msig arg)

  PlayerImpl : PlayerSig → Set
  PlayerImpl sig = (name : MethodName sig) → MethodImpl (MethodSigs sig name)

  ImplTrivial-PS : PlayerImpl Trivial-PS
  ImplTrivial-PS ()

  module _ {I : Set}(sigs : I → PlayerSig) where
    ImplUnion-PS : (∀ i → PlayerImpl (sigs i)) → PlayerImpl (Union-PS sigs)
    ImplUnion-PS fn (i , name) = fn i name

MIMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
MIMorphism IS₁ IS₂ = ∀{sig} → MethodImpl IS₁ sig → MethodImpl IS₂ sig

fmap-MI : ∀{IS₁ IS₂} → FMMorphism IS₁ IS₂ → MIMorphism IS₁ IS₂
fmap-MI m impl arg = m (impl arg)

PIMorphism : (IS₁ IS₂ : InteractionStructure) → Set₁
PIMorphism IS₁ IS₂ = ∀{sig} → PlayerImpl IS₁ sig → PlayerImpl IS₂ sig

fmap-PI : ∀{IS₁ IS₂} → MIMorphism IS₁ IS₂ → PIMorphism IS₁ IS₂
fmap-PI m plr name = m (plr name)

Sig2IS : PlayerSig → InteractionStructure
Command  (Sig2IS sig) = Σ (MethodName sig) (Argument ∘′ MethodSigs sig)
Response (Sig2IS sig) (name , arg) = Result (MethodSigs sig name) arg 
  


{- Idea:
Given a list of playersigs, we can get a corresponding list of implementations.
The list of implementations uses playersigs augmented with earlier ISs.
We can combine the implementations using the usual combine construction.
Can we combine interpretations of these implementations the same way?  Should be doable.
-}

