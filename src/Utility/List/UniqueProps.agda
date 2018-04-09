import ThesisPrelude as TP
module Utility.List.UniqueProps {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Utility.List.Props
open import Utility.List.Elem
open import Utility.List.Functions
open import Algebra.Function
open import Algebra.Equality
open import Algebra.ExactSize

unique-preserves-elem : {a : A}(xs : List A)
                      → a ∈ xs → a ∈ uniques xs
unique-preserves-elem {a}  [] ()
unique-preserves-elem {a}  (x ∷ xs) p with decide-elem x xs
unique-preserves-elem {.a} (a ∷ xs) (here .a .xs)        | yes q = unique-preserves-elem _ q
unique-preserves-elem {.a} (x ∷ xs) (there a .x .xs p)   | yes q = unique-preserves-elem _ p
unique-preserves-elem {.a} (a ∷ xs) (here .a .xs)        | no nq = here a _
unique-preserves-elem {.a} (x ∷ xs) (there a .x .xs p)   | no nq = there a x _ $ unique-preserves-elem _ p
                         
unique-preserves-elem-inv : {a : A}(xs : List A)
                          → a ∈ uniques xs → a ∈ xs
unique-preserves-elem-inv {a} [] ()
unique-preserves-elem-inv {a} (x ∷ xs) p with decide-elem x xs
... | yes q = there a x _ $ unique-preserves-elem-inv _ p
... | no nq with a == x
... | yes refl = here x xs
... | no neq = there a x _ $ unique-preserves-elem-inv _ $ neq-there _ _ neq _ p


uniques-unique : {a : A}(xs : List A)(p : a ∈ xs)
               → (q : a ∈ uniques xs) → q ≡ unique-preserves-elem xs p
uniques-unique [] () q
uniques-unique (x ∷ xs) p q with decide-elem x xs
uniques-unique (a ∷ xs) (here .a .xs)       q                  | yes s = uniques-unique _ s q
uniques-unique (x ∷ xs) (there a .x .xs p)  q                  | yes s = uniques-unique _ p q
uniques-unique (a ∷ xs) (here .a .xs)       (here .a ._)       | no ns = refl
uniques-unique (a ∷ xs) (here .a .xs)       (there .a .a ._ q) | no ns = ⊥-elim $ ns $ unique-preserves-elem-inv _ q
uniques-unique (a ∷ xs) (there .a .a .xs p) (here .a ._)       | no ns = ⊥-elim $ ns p
uniques-unique (x ∷ xs) (there a .x .xs p)  (there .a .x ._ q) | no ns = cong (there a x _) $ uniques-unique _ p q

uniques-gives-singleton : {a : A}(xs : List A)
                        → a ∈ xs → [ a ] ≡ filter (isYes ∘ (_==_ a)) (uniques xs)
uniques-gives-singleton xs p = singleton-elem _ _ $ size1-lem _ (unique-preserves-elem _ p) (uniques-unique _ p)

uniques-idempotent : (xs : List A) → uniques xs ≡ uniques (uniques xs)
uniques-idempotent [] = refl
uniques-idempotent (x ∷ xs) with decide-elem x xs
uniques-idempotent (x ∷ xs) | yes _ = uniques-idempotent xs
uniques-idempotent (x ∷ xs) | no nq with decide-elem x (uniques xs)
uniques-idempotent (x ∷ xs) | no nq | yes q = ⊥-elim (nq (unique-preserves-elem-inv xs q))
uniques-idempotent (x ∷ xs) | no nq | no nq′ rewrite sym (uniques-idempotent xs) = refl
