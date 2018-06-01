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
open import Interaction.Indexed.Joinable

open IxMonad {{...}}

crypto-iso : StateExprState ↔ StateExprState × ⊤
crypto-iso = (λ z → z , tt) , fst , (λ a → refl) , λ { (z , tt) → refl }

CryptoStateIS : IStruct (StateExprState × ⊤)
CryptoStateIS = StateExprIS ⊕-IS CryptoExprIS

CryptoStateTelescope : ∀ n → ISTelescope (replicate n (StateExprState × ⊤))
CryptoStateTelescope zero = ISEmpty
CryptoStateTelescope (suc n) = ISCons CryptoStateIS (CryptoStateTelescope n)

PlayerImplTelescope : ∀{xs} → InfcTelescope xs → Set₁
PlayerImplTelescope {xs} tele = ImplTelescope tele (CryptoStateTelescope (length xs))

SimplePlayerImpl : ∀{xs}{ift : InfcTelescope xs}
                 → (impt : PlayerImplTelescope ift)
                 → SynImpl (InfcTele-QT ift) (ISTele-T (CryptoStateTelescope (length xs))) (combine-state impt)
SimplePlayerImpl = combine-tele 

joinable-SCE-IS : Joinable CryptoStateIS
joinable-SCE-IS = join-joinable-IS joinable-SE-IS joinable-CE-IS 

rewrap-state : ∀ n → foldr _×_ ⊤ (replicate n (StateExprState × ⊤)) → ReplicateState-IS (StateExprState × ⊤) n
rewrap-state zero = id
rewrap-state (suc n) = id ***′ rewrap-state n

rewrap-Impl : ∀ n → SynImpl (ISTele-T (CryptoStateTelescope n)) (Replicate-IS CryptoStateIS n) (rewrap-state n)
rewrap-Impl zero = id-SI
rewrap-Impl (suc n) = binmap-SI id-SI (rewrap-Impl n) 

SynPlayerImpl : ∀{xs}{ift : InfcTelescope xs}
              → (impt : PlayerImplTelescope ift)
              → SynImpl (InfcTele-QT ift)
                        CryptoStateIS
                        (NestedStateJoin CryptoStateIS (bitvec-SE zero , tt) joinable-SCE-IS (length xs)
                          ∘′ rewrap-state (length xs)
                          ∘′ combine-state impt) 
SynPlayerImpl {xs} impt = fmap-IS-SynImpl (NestedJoin CryptoStateIS (bitvec-SE zero , tt) joinable-SCE-IS (length xs))
                          ∘′-SI rewrap-Impl (length xs)
                          ∘′-SI SimplePlayerImpl impt
