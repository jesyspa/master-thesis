module Utility.List.Elem.Index {l}{A : Set l} where

open import ThesisPrelude
open import Utility.List.Elem.Definition
open import Utility.Num

elem-index : ∀{a}{xs : List A} → a ∈ xs → Nat
elem-index (here x xs) = zero
elem-index (there x y xs p) = suc (elem-index p)

elem-index-Inj : ∀{a b}{xs : List A}{p : a ∈ xs}{q : b ∈ xs}
               → elem-index p ≡ elem-index q
               → Σ (a ≡ b) λ eq → transport (λ x → x ∈ xs) eq p ≡ q
elem-index-Inj {p = here a xs}      {here .a .xs} refl    = refl , refl
elem-index-Inj {p = here a xs}      {there b .a .xs q}    ()
elem-index-Inj {p = there a y xs p} {here .y .xs}         ()
elem-index-Inj {p = there a y xs p} {there b .y .xs q} eq with elem-index-Inj (suc-Inj eq)
... | refl , refl = refl , refl
