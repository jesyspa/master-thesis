module Crypto.CPA where

open import ThesisPrelude
open import Crypto.Syntax
open import Crypto.Schemes
open import Utility.List.Elem
open import Utility.Bool

record CpaAdv (E : EncScheme) : Set₁ where
  constructor cpa-adv
  open EncScheme E
  field 
    S  : Set
    A₁ : ∀{O} → CryptoExpr O O ((PT , CT) ∈ O) (PT × PT × S)
    A₂ : ∀{O} → CryptoExpr O O (((PT , CT) ∈ O) × CT × S) Bool

IND-CPA : ∀{O}(E : EncScheme)(A : CpaAdv E) → CryptoExpr O O ⊤ Bool 
IND-CPA {O} E A =
  keygen                  >>>-CE
  make-oracle             >>>-CE
  add-oracle-expr         >>>-CE
  attach-CE tt            >>>-CE
  first-CE A₁             >>>-CE
  coin-expr               >>>-CE
  enc-rnd                 >>>-CE
  second-CE (first-CE A₂) >>>-CE
  is-correct
  where
    open EncScheme E
    open CpaAdv A
    make-oracle : Key → ((PT → CT) 
    enc-rnd′ : (Bool × (PT × PT × S) × Key) → (Bool × ((Key × PT) × S) × Key)
    enc-rnd′ (b , (m₁ , m₂ , s) , k) = b , ((k , (if b then m₁ else m₂)) , s) , k
    enc-rnd : CryptoExpr O O (Bool × (PT × PT × S) × Key) (Bool × (CT × S) × Key)
    enc-rnd = embed-CE enc-rnd′ >>>-CE second-CE (first-CE $ first-CE enc) 
    is-correct′ : Bool × Bool × Key → Bool
    is-correct′ (b , b′ , k) = nxor b b′
    is-correct : CryptoExpr O O (Bool × Bool × Key) Bool
    is-correct = embed-CE is-correct′ 
