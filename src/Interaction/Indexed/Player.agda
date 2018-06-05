module Interaction.Indexed.Player where

open import ThesisPrelude
open import Algebra.Function
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.Implementation
open import Interaction.Indexed.Telescope
open import Interaction.Indexed.CryptoExpr
open import Interaction.Indexed.StateExpr
open import Interaction.Indexed.DistExpr
open import Interaction.Indexed.Joinable
open import Utility.BTAll

open IxMonad {{...}}

CryptoStateTelescope : ∀ n → ISTelescope (ReplicateState-IS (Leaf StateExprState △ Empty) n)
CryptoStateTelescope zero = ISEmpty
CryptoStateTelescope (suc n) = ISCons CryptoExprIS (CryptoStateTelescope n)

PlayerImplTelescope : ∀{xs} → InfcTelescope (foldr _△_ Empty xs) → Set₁
PlayerImplTelescope {xs} tele = ImplTelescope tele (CryptoStateTelescope (length xs))

rewrap-by-eq : ∀ n → ISTele-T (CryptoStateTelescope n) ≡ Replicate-IS CryptoExprIS n
rewrap-by-eq zero = refl
rewrap-by-eq (suc n) rewrite rewrap-by-eq n = refl

SimplePlayerImpl : ∀{xs}{ift : InfcTelescope (foldr _△_ Empty xs)}
                 → (impt : PlayerImplTelescope {xs} ift)
                 → SynImpl (InfcTele-QT ift) (Replicate-IS CryptoExprIS (length xs)) (combine-state impt)
SimplePlayerImpl {xs} rewrite sym $ rewrap-by-eq (length xs) = combine-tele 

PlayerStateJoin : ∀(xs : List (BTree Set))
                → BTAll′ (ReplicateState-IS (Leaf StateExprState △ Empty) (length xs))
                → BTAll′ (Leaf StateExprState △ Empty)
PlayerStateJoin xs = NestedStateJoin CryptoExprIS (leaf (bitvec-SE zero) ▵ empty) joinable-SCE-IS (length xs)

PlayerJoin : ∀(xs : List (BTree Set))
           → ISMorphism (Replicate-IS CryptoExprIS (length xs)) CryptoExprIS (PlayerStateJoin xs)
PlayerJoin xs = NestedJoin CryptoExprIS (leaf (bitvec-SE zero) ▵ empty) joinable-SCE-IS (length xs)

SynPlayerImpl : ∀{xs}{ift : InfcTelescope (foldr _△_ Empty xs)}
              → (impt : PlayerImplTelescope {xs} ift)
              → SynImpl (InfcTele-QT ift) CryptoExprIS (PlayerStateJoin xs ∘′ combine-state impt) 
SynPlayerImpl {xs} impt = fmap-IS-SynImpl (PlayerJoin xs) ∘′-SI SimplePlayerImpl {xs} impt
