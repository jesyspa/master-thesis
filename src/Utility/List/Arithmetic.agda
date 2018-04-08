open import Probability.Class using (Probability)
module Utility.List.Arithmetic (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Algebra.MonoidHelpers
open import Algebra.Function
open import Algebra.SemiringProps Q
open import Algebra.Preorder Q
open import Probability.Class
open import Probability.PropsClass Q
open import Utility.List.Lookup
open import Utility.List.Props
open import Utility.List.SlowArithmetic Q public

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open Probability PQ
  open import Algebra.Monoid Q 
  open SemiringProps srprops
  open PreorderProps poprops
  open CommMonoidProps +-is-comm-monoid
  open MonoidProps forget-comm

  sum-const-mul : ∀{l}{A : Set l}(q : Q)
                → (xs : List A)
                → sum (map (const q) xs) ≡ q * embed (length xs)
  sum-const-mul q [] = zro-right-nil q
  sum-const-mul q (x ∷ xs) rewrite sym (sum-rewrite q (map (const q) xs)) | sum-const-mul q xs =
    q + q * embed (length xs)
      ≡⟨ cong (λ e → e + q * embed (length xs)) (*-unit-right q) ⟩
    q * one + q * embed (length xs)
      ≡⟨ +*-left-dist q one (embed (length xs)) ⟩ʳ
    q * (one + embed (length xs))
      ≡⟨ cong (_*_ q) (+-comm one (embed (length xs))) ⟩
    q * (embed (length xs) + one)
    ∎

  sum-preserves-≤ : ∀{l}{A : Set l}
                  → (f g : A → Q)
                  → (xs : List A)
                  → (∀ a → f a ≤ g a)
                  → sum (map f xs) ≤ sum (map g xs)
  sum-preserves-≤ f g [] pf = ≤-refl (sum [])
  sum-preserves-≤ f g (x ∷ xs) pf
    rewrite sym (sum-rewrite (f x) (map f xs))
          | sym (sum-rewrite (g x) (map g xs)) = ≤-dist-+ (pf x) (sum-preserves-≤ f g xs pf)
