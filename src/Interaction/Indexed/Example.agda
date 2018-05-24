module Interaction.Indexed.Example where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.FreeMonad 
open import Interaction.Indexed.Implementation 
open import Interaction.Indexed.CryptoExpr 
open import Interaction.Indexed.StateExpr 
open import Interaction.Indexed.Telescope 
open import Utility.Vector

open InteractionStructure
open ISMorphism

challengerInfc : InteractionStructure (⊤ × ⊤)
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

  adversaryInfc : InteractionStructure (⊤ × ⊤ × ⊤ × ⊤)
  Command  adversaryInfc _               = CommandAdv
  Response adversaryInfc generate-msgs   = PT × PT
  Response adversaryInfc (guess-which _) = Bool
  next     adversaryInfc {s} _           = s

  totalInfcTelescope : InfcTelescope (⊤ ∷ ⊤ ∷ ⊤ ∷ [])
  totalInfcTelescope = InfcCons {!challengerInfc!} $ InfcCons {!!} $ InfcCons {!!} InfcEmpty

{-
  challengerImpl : SynImpl challengerInfc ( CE (encSchemeInfc ∷ adversaryInfc ∷ []))
  challengerImpl tt =
    Invoke-FM (true , false , keygen)                λ k →
    Invoke-FM (true , true , false , generate-msgs)  λ m →
    Invoke-FM (false , uniform 1)                    λ bv →
    Invoke-FM (true , false , enc k (if head bv
                                     then fst m
                                     else snd m))    λ ct →
    Invoke-FM (true , true , false , guess-which ct) λ b →
    Return-FM (isYes (head bv == b))
    -}

{-
  encSchemeImplType : Set
  encSchemeImplType = SynImpl encSchemeInfc (Extend*-IS CE [])

  adversaryImplType : Set
  adversaryImplType = SynImpl adversaryInfc (Extend*-IS CE [])

  bindEncScheme : encSchemeImplType → SynImpl challengerInfc (Extend*-IS CE [ adversaryInfc ])
  bindEncScheme scheme = CombineHead {challengerInfc} {encSchemeInfc} {CE} {[ adversaryInfc ]} challengerImpl (WeakenBy {encSchemeInfc} {CE} {[]} adversaryInfc scheme)
 
  game : encSchemeImplType → adversaryImplType → ImplTelescope (challengerInfc ∷ adversaryInfc ∷ []) (CE ∷ CE ∷ [])
  game scheme adv = Cons-IT (bindEncScheme scheme) (Cons-IT adv Nil-IT)


  game′ : encSchemeImplType → adversaryImplType → SynImpl challengerInfc CE
  game′ scheme adv = free-SynImpl (BinMatch-IS _ _ id-IS Coproduct-RightUnit-IS) ∘′-SI CombineSyn* (game scheme adv) ∘′-SI free-SynImpl (InclL-IS _ _)

-}
