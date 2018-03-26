module Interaction.Complete.Player where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 

open InteractionStructure
open ISMorphism

record Method (IS : InteractionStructure) : Set₁ where
  field
    Argument : Set
    Result : Argument → Set
    Impl : (arg : Argument) → FreeMonad IS (Result arg)
open Method

Method-fmap : ∀{IS₁ IS₂} → ISMorphism IS₁ IS₂ → Method IS₁ → Method IS₂
Argument (Method-fmap m mth)     = Argument mth
Result   (Method-fmap m mth) arg = Result mth arg
Impl     (Method-fmap m mth) arg = action-FM m (Impl mth arg)

    
record Player (IS : InteractionStructure) : Set₁ where
  field
    MethodName : Set
    MethodImpl : MethodName → Method IS
open Player

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

