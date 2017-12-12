module AbstractDist where

open import MyPrelude
open import BitVec

abstract
  data ADist (A : Set) : Set where
  data Carrier : Set where

postulate
  returnA : ∀{A} → A → ADist A
  _>>=A_ : ∀{A B} → ADist A → (A → ADist B) → ADist B

  uniformA : ∀ n → ADist (BitVec n)

  sample : ∀{A} → {{_ : Eq A}} → ADist A → A → Carrier

data _≡A_ {A} {{_ : Eq A}} : ADist A → ADist A → Set where
  ext-≡A : (da db : ADist A) → ((a : A) → sample da a ≡ sample db a) → da ≡A db

