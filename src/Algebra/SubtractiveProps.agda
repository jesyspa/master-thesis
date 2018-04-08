open import ThesisPrelude using (Semiring; Subtractive)
module Algebra.SubtractiveProps (A : Set){{SRA : Semiring A}}{{SA : Subtractive A}} where

open import ThesisPrelude

record SubtractiveProps : Set where
  field
    adj-plus : {a b c : A} → a ≡ b + c → a - c ≡ b
    adj-plus-inv : {a b c : A} → a - c ≡ b → a ≡ b + c
    neg-zro  : (a : A) → zro - a ≡ negate a

open import Algebra.SemiringProps A
module _ {{SRP : SemiringProps}}{{SP : SubtractiveProps}} where
  open SemiringProps SRP
  open SubtractiveProps SP
  sub-unit-right : (a : A) → a - zro ≡ a
  sub-unit-right a = adj-plus (+-unit-right a)

  sub-cancelling : (a : A) → a - a ≡ zro
  sub-cancelling a = adj-plus (+-unit-left a)

  plus-sub-cancelling : (a b : A) → a ≡ (a - b) + b
  plus-sub-cancelling a b = adj-plus-inv refl

  sub-triangle : (a b c : A) → a - c ≡ (a - b) + (b - c)
  sub-triangle a b c = adj-plus (
    a
      ≡⟨ plus-sub-cancelling a b ⟩
    (a - b) + b
      ≡⟨ cong (λ e → (a - b) + e) (plus-sub-cancelling b c) ⟩
    (a - b) + ((b - c) + c)
      ≡⟨ +-assoc (a - b) (b - c) c ⟩
    (a - b) + (b - c) + c
    ∎)
  
