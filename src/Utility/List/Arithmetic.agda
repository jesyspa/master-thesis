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
open import Utility.List.Elem
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
  sum-const-mul q (x ∷ xs) rewrite sum-rewrite′ q (map (const q) xs) | sum-const-mul q xs =
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
    rewrite sum-rewrite′ (f x) (map f xs)
          | sum-rewrite′ (g x) (map g xs) = ≤-dist-+ (pf x) (sum-preserves-≤ f g xs pf)

  nonnegative-sum : (xs : List Q)
                  → (∀{p} → p ∈ xs → zro ≤ p)
                  → zro ≤ sum xs
  nonnegative-sum [] pf = ≤-refl zro
  nonnegative-sum (x ∷ xs) pf
    rewrite sum-rewrite′ x xs = transport (λ e → e ≤ x + sum xs)
                                          (sym $ +-unit-left zro)
                                          (≤-dist-+ (pf (here x _))
                                                    (nonnegative-sum xs λ pt → pf (there _ _ _ pt)))

  sum-bounds-individuals : {q : Q}{xs : List Q}
                         → q ∈ xs
                         → (∀{p} → p ∈ xs → zro ≤ p)
                         → q ≤ sum xs
  sum-bounds-individuals (here x xs) nn
    rewrite sum-rewrite′ x xs = transport (λ e → e ≤ x + sum xs)
                                          (sym $ +-unit-right x)
                                          (≤-dist-+ (≤-refl x)
                                                    (nonnegative-sum xs (λ pt → nn (there _ _ _ pt))))
  sum-bounds-individuals (there x y xs pt) nn
    rewrite sum-rewrite′ y xs = transport (λ e → e ≤ y + sum xs)
                                          (sym $ +-unit-left x)
                                          (≤-dist-+ (nn (here y _))
                                                    (sum-bounds-individuals pt λ pt′ → nn (there _ _ _ pt′)))
                         
