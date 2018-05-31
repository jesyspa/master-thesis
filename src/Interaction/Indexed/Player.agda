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

-- A player has some specific interface and is implemented in terms of a StateExpr S ⊕ CryptoExpr 
-- The player may be aware of what players it depends on (since it needs to contain their state).

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

{-
SquishImpl : ∀ n → SynImpl (ISTele-T $ CryptoStateTelescope n) CryptoStateIS (squish-states n)
SquishImpl zero ()
SquishImpl (suc n) {sa , sb} (left (left (modify-SE S′ f))) = {!!}
SquishImpl (suc n) {sa , sb} (left (right (uniform-CE k))) = Invoke-FM (right (uniform-CE k)) λ r → Return-FM (StrongV r refl)
SquishImpl (suc n) {sa , sb} (right c) = {!SquishImpl n ?!}
-}

joinable-SCE-IS : Joinable CryptoStateIS
joinable-SCE-IS = join-joinable-IS joinable-SE-IS joinable-CE-IS 

PlayerImpl : ∀{xs}{ift : InfcTelescope xs}
           → (impt : PlayerImplTelescope ift)
           → SynImpl (InfcTele-QT ift) CryptoStateIS (NestedStateJoin CryptoStateIS (bitvec-SE zero , tt) joinable-SCE-IS (length xs) ∘′ {!!} ∘′ combine-state impt) 
PlayerImpl {xs} impt = fmap-IS-SynImpl (NestedJoin CryptoStateIS (bitvec-SE zero , tt) joinable-SCE-IS {!length xs!} ) ∘′-SI SimplePlayerImpl impt
