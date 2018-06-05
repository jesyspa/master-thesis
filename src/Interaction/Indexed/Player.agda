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

SimplePlayerImpl : ∀{xs}{ift : InfcTelescope (foldr _△_ Empty xs)}
                 → (impt : PlayerImplTelescope {xs} ift)
                 → SynImpl (InfcTele-QT ift) (ISTele-T (CryptoStateTelescope (length xs))) (combine-state impt)
SimplePlayerImpl = combine-tele 

{-
rewrap-state : ∀ n → foldr _×_ ⊤ (replicate n (StateExprState × ⊤)) → BTAll′ (ReplicateState-IS (Leaf StateExprState △ Empty) n)
rewrap-state zero = id
rewrap-state (suc n) = id ***′ rewrap-state n
-}

rewrap-Impl : ∀ n → SynImpl (ISTele-T (CryptoStateTelescope n)) (Replicate-IS CryptoExprIS n) ?
rewrap-Impl zero = id-SI
rewrap-Impl (suc n) = binmap-SI id-SI (rewrap-Impl n) 

SynPlayerImpl : ∀{xs}{ift : InfcTelescope (foldr _△_ Empty xs)}
              → (impt : PlayerImplTelescope {xs} ift)
              → SynImpl (InfcTele-QT ift)
                        CryptoExprIS
                        (NestedStateJoin CryptoExprIS (leaf (bitvec-SE zero) ▵ empty) joinable-SCE-IS (length xs)
                          ∘′ ? -- rewrap-state (length xs)
                          ∘′ combine-state impt) 
SynPlayerImpl {xs} impt = fmap-IS-SynImpl (NestedJoin CryptoExprIS (leaf (bitvec-SE zero) ▵ empty) joinable-SCE-IS (length xs))
                          ∘′-SI rewrap-Impl (length xs)
                          ∘′-SI SimplePlayerImpl {xs} impt
