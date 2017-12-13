module Carrier.Abstract where

open import ThesisPrelude
open import Carrier.Class

abstract
  data ACarrier : Set where

postulate
  instance
    ACarrierSemiring : Semiring ACarrier
    ACarrierOrd : Ord ACarrier
    ACarrierCarrierProps : CarrierProps ACarrier
