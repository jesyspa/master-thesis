module Interaction.Complete.CryptoExpr  where

open import ThesisPrelude
open import Utility.Vector
open import Interaction.Complete.InteractionStructure
open import Interaction.Complete.SyntacticImplementation

data CryptoExprCmd : Set where
  uniform-CE : Nat → CryptoExprCmd

CryptoExprResp : CryptoExprCmd → Set
CryptoExprResp (uniform-CE n) = BitVec n

open InteractionStructure
CryptoExprIS : InteractionStructure
Command  CryptoExprIS = CryptoExprCmd
Response CryptoExprIS = CryptoExprResp

GameIS : Set → InteractionStructure
Command  (GameIS A) = ⊤
Response (GameIS A) tt = A

infixr 5 _◂_
data CryptoTelescope : List InteractionStructure → Set₁ where
  CE-Nil  : CryptoTelescope []
  _◂_ : ∀{IS ISs}
      → SynImpl IS (Extend*-IS CryptoExprIS ISs)
      → CryptoTelescope ISs
      → CryptoTelescope (IS ∷ ISs)

buildCT : ∀{ISs} → CryptoTelescope ISs → SynImpl (BinCoproduct*-IS ISs) CryptoExprIS
buildCT CE-Nil = Init-SynI
buildCT (si ◂ ct) = BinMatch-SynI (BinMatch-SynI id-SynI (buildCT ct) ∘′-SI si) (buildCT ct)

buildGame : ∀{A ISs} → CryptoTelescope (GameIS A ∷ ISs) → SynImpl (GameIS A) CryptoExprIS
buildGame ct = buildCT ct ∘′-SI free-SynImpl (InclL-IS _ _)
