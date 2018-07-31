module Interaction.Complete.StateExample where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Combine 
open import Interaction.Complete.Implementation 
open import Interaction.Complete.SyntacticImplementation 
open import Utility.Vector
open import Utility.State
open import Distribution.Class

open InteractionStructure
open ISMorphism

data CommandCE : Set where
  uniform  : Nat → CommandCE

CE : InteractionStructure
Command  CE = CommandCE
Response CE (uniform n)  = BitVec n

CE-impl : (D : Set → Set){{_ : DistMonad D}} → Implementation CE D
CE-impl D {{DM}} (uniform n) = DistMonad.uniform DM n

data CommandStateE (S : Set) : Set where
  modState : (S → S) → CommandStateE S

StateE : (S : Set) → InteractionStructure
Command  (StateE S) = CommandStateE S
Response (StateE S) (modState f) = S

InclL-SE : (S₁ S₂ : Set) → ISMorphism (StateE S₁) (StateE (S₁ × S₂))
CommandF  (InclL-SE S₁ S₂) (modState f) = modState (first f)
ResponseF (InclL-SE S₁ S₂) {modState f} r = fst r

InclR-SE : (S₁ S₂ : Set) → ISMorphism (StateE S₂) (StateE (S₁ × S₂))
CommandF  (InclR-SE S₁ S₂) (modState f) = modState (second f)
ResponseF (InclR-SE S₁ S₂) {modState f} r = snd r

addState : (S : Set) → InteractionStructure → InteractionStructure
addState S IS = IS ⊎-IS StateE S

implState : ∀{S IS M}{{_ : Monad M}} → Implementation IS M → Implementation (addState S IS) (StateT S M)
implState I (false , c) = liftT (I c)
implState I (true , modState f) = modifyT f

combineState : ∀{IS S₁ S₂}
             → SynImpl (addState S₁ IS ⊎-IS addState S₂ IS) (addState (S₁ × S₂) IS)
combineState {IS} {S₁} {S₂} = BinMatch-SynI l r
  where
    l : SynImpl (addState S₁ IS) (addState (S₁ × S₂) IS)
    l = BinJoin-SynI id-SynI (free-SynImpl $ InclL-SE _ _)
    r : SynImpl (addState S₂ IS) (addState (S₁ × S₂) IS)
    r = BinJoin-SynI id-SynI (free-SynImpl $ InclR-SE _ _)


challengerInfc : InteractionStructure
Command  challengerInfc = ⊤
Response challengerInfc tt = Bool

module _ (K PT CT : Set) where
  data CommandGame : Set where
    keygen : CommandGame
    enc    : K → PT → CommandGame

  encSchemeInfc : InteractionStructure
  Command  encSchemeInfc  = CommandGame
  Response encSchemeInfc keygen     = K
  Response encSchemeInfc (enc k pt) = CT

  data CommandAdv : Set where
    generate-msgs : CommandAdv
    guess-which   : CT → CommandAdv

  adversaryInfc : InteractionStructure
  Command  adversaryInfc = CommandAdv
  Response adversaryInfc generate-msgs   = PT × PT
  Response adversaryInfc (guess-which _) = Bool

  challengerImpl : ∀{S} → SynImpl challengerInfc (Extend*-IS (addState S CE) (encSchemeInfc ∷ adversaryInfc ∷ []))
  challengerImpl tt =
    Invoke-FM (true , false , keygen)                λ k →
    Invoke-FM (true , true , false , generate-msgs)  λ m →
    Invoke-FM (false , false , uniform 1)            λ bv →
    Invoke-FM (true , false , enc k (if head bv
                                     then fst m
                                     else snd m))    λ ct →
    Invoke-FM (true , true , false , guess-which ct) λ b →
    Return-FM (isYes (head bv == b))

  encSchemeImplType : Set → Set
  encSchemeImplType S = SynImpl encSchemeInfc (Extend*-IS (addState S CE) [])

  adversaryImplType : Set → Set
  adversaryImplType S = SynImpl adversaryInfc (Extend*-IS (addState S CE) [])

  bindEncScheme : ∀{S} → encSchemeImplType S → SynImpl challengerInfc (Extend*-IS (addState S CE) [ adversaryInfc ])
  bindEncScheme {S} scheme = CombineHead {_} {_} {_} {[ adversaryInfc ]} challengerImpl (WeakenBy {_} {_} {[]} adversaryInfc scheme)
 
  game : ∀{S₁ S₂} → encSchemeImplType S₁ → adversaryImplType S₂ → ImplTelescope (challengerInfc ∷ adversaryInfc ∷ []) (addState S₁ CE ∷ addState S₂ CE ∷ [])
  game scheme adv = Cons-IT (bindEncScheme scheme) (Cons-IT adv Nil-IT)

  game′ : ∀{S₁ S₂} → encSchemeImplType S₁ → adversaryImplType S₂ → SynImpl challengerInfc (addState (S₁ × S₂) CE)
  game′ scheme adv = combineState ∘′-SI BinJoin-SynI id-SynI (free-SynImpl Coproduct-RightUnit-IS) ∘′-SI CombineSyn* (game scheme adv) ∘′-SI free-SynImpl (InclL-IS _ _)



