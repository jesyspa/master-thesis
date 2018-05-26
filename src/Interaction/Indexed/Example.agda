module Interaction.Indexed.Example where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Interaction.Indexed.Implementation 
open import Interaction.Indexed.CryptoExpr 
open import Interaction.Indexed.StateExpr 
open import Interaction.Indexed.Telescope 
open import Utility.Vector

open InteractionStructure
open ISMorphism

challengerInfc : InteractionStructure (⊤ × ⊤ × ⊤ × ⊤)
Command  challengerInfc _ = ⊤
Response challengerInfc tt = Bool
next     challengerInfc {s} r  = s

module _ (K PT CT : Set) where
  data CommandGame : Set where
    keygen : CommandGame
    enc    : K → PT → CommandGame

  encSchemeInfc : InteractionStructure (⊤ × ⊤ × ⊤)
  Command  encSchemeInfc _          = CommandGame
  Response encSchemeInfc keygen     = K
  Response encSchemeInfc (enc k pt) = CT
  next     encSchemeInfc {s} _      = s

  data CommandAdv : Set where
    generate-msgs : CommandAdv
    guess-which   : CT → CommandAdv

  adversaryInfc : InteractionStructure (⊤ × ⊤)
  Command  adversaryInfc _               = CommandAdv
  Response adversaryInfc generate-msgs   = PT × PT
  Response adversaryInfc (guess-which _) = Bool
  next     adversaryInfc {s} _           = s

  totalInfcTelescope : InfcTelescope (⊤ ∷ ⊤ ∷ ⊤ ∷ [])
  totalInfcTelescope = InfcCons challengerInfc $ InfcCons encSchemeInfc $ InfcCons adversaryInfc InfcEmpty

  totalISTelescope : ISTelescope (⊤ ∷ ⊤ ∷ ⊤ ∷ [])
  totalISTelescope = ISCons CryptoExprIS $ ISCons CryptoExprIS $ ISCons CryptoExprIS ISEmpty

  tailInfcTelescope : ∀{IS ISs} → InfcTelescope (IS ∷ ISs) → InfcTelescope ISs
  tailInfcTelescope (InfcCons _ tele) = tele

  challengerImpl : SynImpl challengerInfc (BinTensor-IS CryptoExprIS (InfcTele-QT (tailInfcTelescope totalInfcTelescope))) id
  challengerImpl {_ , _ , _ , _} _ =
    Invoke-FM (right $ left          $ keygen)           λ k → 
    Invoke-FM (right $ right $ left  $ generate-msgs)    λ m → 
    Invoke-FM (left                  $ uniform-CE 1)     λ bv → 
    Invoke-FM (right $ left          $ enc k
                (if head bv then fst m else snd m))      λ ct →
    Invoke-FM (right $ right $ left  $ guess-which ct)   λ b →
    Return-FM (StrongV (isYes (head bv == b)) refl) 

  encSchemeImplType : Set
  encSchemeImplType = SynImpl encSchemeInfc (BinTensor-IS CryptoExprIS (InfcTele-QT (InfcCons adversaryInfc InfcEmpty))) (first id)

  adversaryImplType : Set
  adversaryImplType = SynImpl adversaryInfc (BinTensor-IS CryptoExprIS (InfcTele-QT InfcEmpty)) (first id)

  game : encSchemeImplType → adversaryImplType → ImplTelescope totalInfcTelescope totalISTelescope
  game scheme adv = ImplCons id challengerImpl $ ImplCons id scheme $ ImplCons id adv $ ImplEmpty

  game′ : (scheme : encSchemeImplType)
        → (adv : adversaryImplType)
        → SynImpl (InfcTele-QT totalInfcTelescope) (ISTele-T totalISTelescope) (combine-state $ game scheme adv)
  game′ scheme adv {s} = combine-tele (game scheme adv) {s}
