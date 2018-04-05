open import Distribution.Class
open import Distribution.PropsClass
module Examples.Epsilon (M : Set → Set){{DM : DistMonad M}}{{DMP : DistMonadProps M}} where

open import ThesisPrelude
open import Probability.Class
open import Probability.PropsClass

open DistMonad DM
open DistMonadProps DMP
open Probability probability-super
open ProbabilityProps is-probability

Q = probability

open import Algebra.SubtractiveProps Q
open import Algebra.SemiringProps Q
open import Algebra.Preorder Q

open SubtractiveProps subprops
open SemiringProps srprops 
open PreorderProps poprops

module _ {A}{{_ : Eq A}} where
  bounded-dist-diff-refl : (ε : Q)(D : M A) → (zro ≤ ε) → bounded-dist-diff D D ε
  bounded-dist-diff-refl ε D pf a = bounded-diff-refl _ pf
  
  bounded-dist-diff-sym : (ε : Q){D₁ D₂ : M A}
                        → bounded-dist-diff D₁ D₂ ε
                        → bounded-dist-diff D₂ D₁ ε
  bounded-dist-diff-sym ε pf a = bounded-diff-sym (pf a)
  
  bounded-dist-diff-trans : (ε₁ ε₂ : Q){D₁ D₂ D₃ : M A}
                          → bounded-dist-diff D₁ D₂ ε₁
                          → bounded-dist-diff D₂ D₃ ε₂
                          → bounded-dist-diff D₁ D₃ (ε₁ + ε₂)
  bounded-dist-diff-trans ε₁ ε₂ bd₁ bd₂ a = bounded-diff-trans (bd₁ a) (bd₂ a)

silly-coin : bounded-dist-diff coin (return true) (negpow2 1) 
silly-coin false = lem
  where simpl-left : sample coin false ≡ negpow2 1
        simpl-left = sym $ coin-is-fair false
        simpl-right : sample {Bool} (return true) false ≡ zro
        simpl-right = sym $ return-sample-0 true false λ ()
        lem : abs (sample coin false - sample {Bool} (return true) false) ≤ negpow2 1
        lem rewrite simpl-left
                  | simpl-right
                  | sub-unit-right (negpow2 1)
                  | sym (abs-pos (negpow2 1) (embed-< (negpow-pos 1))) = ≤-refl (negpow2 1)
silly-coin true  = lem
  where simpl-left : sample coin true ≡ negpow2 1
        simpl-left = sym $ coin-is-fair true
        simpl-right : sample {Bool} (return true) true ≡ one
        simpl-right = sym $ return-sample-1 true
        pow2-expand : one ≡ negpow2 1 + negpow2 1
        pow2-expand rewrite pow2-negpow2-cancel 1 =
          (zro + one + one) * negpow2 1
            ≡⟨ cong (λ e → (e + one) * negpow2 1) (+-unit-left one) ⟩ʳ
          (one + one) * negpow2 1
            ≡⟨ +*-right-dist one one (negpow2 1)  ⟩
          one * negpow2 1 + one * negpow2 1
            ≡⟨ cong₂ _+_ (*-unit-left (negpow2 1)) (*-unit-left (negpow2 1)) ⟩ʳ
          negpow2 1 + negpow2 1
          ∎
        lem : abs (sample coin true - sample {Bool} (return true) true) ≤ negpow2 1
        lem rewrite simpl-left
                  | simpl-right
                  | abs-sub-sym (negpow2 1) one
                  | adj-plus pow2-expand
                  | sym (abs-pos (negpow2 1) (embed-< (negpow-pos 1)))
                  = ≤-refl (negpow2 1)

