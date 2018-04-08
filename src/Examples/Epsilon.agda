open import Distribution.Class
open import Distribution.PropsClass
module Examples.Epsilon (M : Set → Set){{DM : DistMonad M}}{{DMP : DistMonadProps M}} where

open import ThesisPrelude
open import Probability.Class
open import Probability.PropsClass
open import Algebra.FiniteSet
open import Utility.List

open DistMonad DM
open DistMonadProps DMP
open Probability probability-super
open ProbabilityProps is-probability

Q = probability

open import Utility.List.Arithmetic Q
open import Algebra.SubtractiveProps Q
open import Algebra.SemiringProps Q
open import Algebra.Preorder Q

open SubtractiveProps subprops
open SemiringProps srprops 
open PreorderProps poprops

module _ {A}{{FS : FiniteSet A}} where
  open UniqueListable (ListableUniqueListable (FiniteSetListable {{FS}}))
  open Listable super-Enumeration

  dist-diff-refl : (D : M A) → zro ≡ dist-diff D D
  dist-diff-refl D = dist-0-eq-inv D D (≡D-refl _)

  bounded-dist-diff-refl : (ε : Q)(D : M A) → (zro ≤ ε) → bounded-dist-diff D D ε
  bounded-dist-diff-refl ε D pf rewrite sym (dist-diff-refl D) = pf
  
  dist-diff-sym : (D₁ D₂ : M A) → dist-diff D₁ D₂ ≡ dist-diff D₂ D₁
  dist-diff-sym D₁ D₂ = cong sum $ map-ext (λ a → abs (sample D₁ a - sample D₂ a))
                                           (λ a → abs (sample D₂ a - sample D₁ a))
                                           (λ a → abs-sub-sym (sample D₁ a) (sample D₂ a))
                                           ListEnumeration

  bounded-dist-diff-sym : (ε : Q){D₁ D₂ : M A}
                        → bounded-dist-diff D₁ D₂ ε
                        → bounded-dist-diff D₂ D₁ ε
  bounded-dist-diff-sym ε {D₁} {D₂} pf rewrite sym (dist-diff-sym D₁ D₂) = pf
  
  dist-diff-trans : (D₁ D₂ D₃ : M A) → dist-diff D₁ D₃ ≤ dist-diff D₁ D₂ + dist-diff D₂ D₃
  dist-diff-trans D₁ D₂ D₃ = ≤-trans lem0 lem1
    where 
        lem0 : dist-diff D₁ D₃
             ≤ sum (map (λ a → abs (sample D₁ a - sample D₂ a) + abs (sample D₂ a - sample D₃ a)) ListEnumeration)
        lem0 = sum-preserves-≤  (λ a → abs (sample D₁ a - sample D₃ a))
                                (λ a → abs (sample D₁ a - sample D₂ a) + abs (sample D₂ a - sample D₃ a))
                                ListEnumeration
                                (λ a → abs-triangle (sample D₁ a) (sample D₂ a) (sample D₃ a))
        lem1 : sum (map (λ a → abs (sample D₁ a - sample D₂ a) + abs (sample D₂ a - sample D₃ a)) ListEnumeration)
             ≤ dist-diff D₁ D₂ + dist-diff D₂ D₃
        lem1 rewrite sum-map-dist (λ a → abs (sample D₁ a - sample D₂ a))
                                  (λ a → abs (sample D₂ a - sample D₃ a))
                                  ListEnumeration
                     = ≤-refl _

  bounded-dist-diff-trans : (ε₁ ε₂ : Q){D₁ D₂ D₃ : M A}
                          → bounded-dist-diff D₁ D₂ ε₁
                          → bounded-dist-diff D₂ D₃ ε₂
                          → bounded-dist-diff D₁ D₃ (ε₁ + ε₂)
  bounded-dist-diff-trans ε₁ ε₂ {D₁} {D₂} {D₃} bd₁ bd₂ = ≤-trans (dist-diff-trans D₁ D₂ D₃) (≤-dist-+ bd₁ bd₂)
      

{-
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


-}
