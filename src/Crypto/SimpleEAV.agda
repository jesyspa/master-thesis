module Crypto.SimpleEAV where

open import ThesisPrelude
open import Crypto.Schemes
open import Crypto.Syntax
open import Utility.Bool

record SimpleEavAdv (E : EncScheme) : Set₁ where
  constructor simple-eav-adv
  open EncScheme E
  field 
    A₁ : ∀{O} → CryptoExpr O O ⊤ (PT × PT)
    A₂ : ∀{O} → CryptoExpr O O CT Bool
    -- How about asking the adversary to prove that his
    -- message is not the encrypted one? 
    -- ie. defend from bad-events on the type-level!


simple-IND-EAV : ∀{O}(E : EncScheme)(A : SimpleEavAdv E) → CryptoExpr O O ⊤ Bool 
simple-IND-EAV {O} E A =
  keygen                  >>>-CE
  attach-CE tt            >>>-CE
  first-CE A₁             >>>-CE
  coin-expr               >>>-CE
  enc-rnd                 >>>-CE
  second-CE (first-CE A₂) >>>-CE
  is-correct
  where
    open EncScheme E
    open SimpleEavAdv A
    enc-rnd′ : (Bool × (PT × PT) × Key) → (Bool × (Key × PT) × Key)
    enc-rnd′ (b , (m₁ , m₂) , k) = b , (k , (if b then m₁ else m₂)) , k
    enc-rnd : CryptoExpr O O (Bool × (PT × PT) × Key) (Bool × CT × Key)
    enc-rnd = embed-CE enc-rnd′ >>>-CE second-CE (first-CE enc) 
    is-correct′ : Bool × Bool × Key → Bool
    is-correct′ (b , b′ , k) = nxor b b′
    is-correct : CryptoExpr O O (Bool × Bool × Key) Bool
    is-correct = embed-CE is-correct′ 
