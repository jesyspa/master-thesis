module Crypto where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import FreeMonad using (Free; Step; Stop; TS; return; _>>=_)

data CryptoCmd : Set where
  RndVector : ℕ → CryptoCmd
  FairCoin : CryptoCmd

-- I don't know how to implement this
data Coin : Set where
  coin : Coin

CryptoResp : CryptoCmd -> Set
CryptoResp (RndVector n) = Vec Bool n
CryptoResp FairCoin = Coin

cryptoTS : TS
TS.C (cryptoTS) = CryptoCmd
TS.R (cryptoTS) = CryptoResp

Crypto : Set → Set
Crypto = Free cryptoTS

random : (n : ℕ) → Crypto (Vec Bool n)
random n = Step (RndVector n) Stop

fairCoin : Crypto Coin
fairCoin = Step FairCoin Stop
