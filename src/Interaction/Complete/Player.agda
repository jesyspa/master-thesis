module Interaction.Complete.Player where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 

open InteractionStructure
open ISMorphism

record MethodSig : Set₁ where
  field
    Argument : Set
    Result : Argument → Set
open MethodSig

record PlayerSig : Set₁ where
  field
    MethodName : Set
    MethodSigs : MethodName → MethodSig
open PlayerSig


{- Idea:
Given a list of playersigs, we can get a corresponding list of implementations.
The list of implementations uses playersigs augmented with earlier ISs.
We can combine the implementations using the usual combine construction.
Can we combine interpretations of these implementations the same way?  Should be doable.
-}


       

{-
Method : ∀{IS}(sig : MethodSig IS)(arg : Argument sig) → FreeMonad IS (Result sig arg)
Method = 
-}


{-
    
record Player (IS : InteractionStructure) : Set₁ where
  field
    MethodName : Set
    MethodImpl : MethodName → Method IS
open Player

EmptyPlayer : ∀{IS} → Player IS
MethodName EmptyPlayer = ⊥
MethodImpl EmptyPlayer ()

MkCommands : ∀{IS} → Player IS → Set
MkCommands plr = Σ (MethodName plr) (λ n → Argument (MethodImpl plr n))

MkResponses : ∀{IS} → (plr : Player IS) → MkCommands plr → Set
MkResponses plr (n , arg) = Result (MethodImpl plr n) arg

Augment : ∀{ISₚ} → Player ISₚ → InteractionStructure → InteractionStructure
Command  (Augment plr IS) = Command IS ⊎ MkCommands plr
Response (Augment plr IS) (left  c) = Response IS c
Response (Augment plr IS) (right c) = MkResponses plr c

Augment-embed : ∀{ISₚ IS}(plr : Player ISₚ) → ISMorphism IS (Augment plr IS)
CommandF  (Augment-embed plr) c = left c
ResponseF (Augment-embed plr) r = r

Augment-fmap : ∀{ISₚ IS IS′}(plr : Player ISₚ) → ISMorphism IS IS′ → ISMorphism (Augment plr IS) (Augment plr IS′)
CommandF  (Augment-fmap plr m) (left  c) = left (CommandF m c)
CommandF  (Augment-fmap plr m) (right c) = right c
ResponseF (Augment-fmap plr m) {left  c} r = ResponseF m r
ResponseF (Augment-fmap plr m) {right c} r = r

Augment-bind : ∀{ISₚ IS IS′}(plr : Player ISₚ) → ISMorphism IS (Augment plr IS′) → ISMorphism (Augment plr IS) (Augment plr IS′)
CommandF  (Augment-bind plr m) (left  c) = CommandF m c
CommandF  (Augment-bind plr m) (right c) = right c
ResponseF (Augment-bind plr m) {left  c} r = ResponseF m r
ResponseF (Augment-bind plr m) {right c} r = r


-}
