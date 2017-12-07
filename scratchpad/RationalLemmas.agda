{-# OPTIONS --allow-unsolved-metas #-}
module RationalLemmas where

open import MyPrelude
open import NatLemmas

rat-one-lem-try2 : {x : Rational} → one * x ≡ x
rat-one-lem-try2 {Rational.ratio p q {{nz}} prf} with one * Rational.ratio p q prf
... | Rational.ratio p2 q2 {{nz'}} prf' = {!!}

rat-one-lem : {x : Rational} → one * x ≡ x
rat-one-lem {Rational.ratio p q {{nz}} prf} = 
  mkratio 1 1 * Rational.ratio p q prf
    ≡⟨ refl ⟩
  Rational.ratio 1 1 refl * Rational.ratio p q prf
    ≡⟨ cong {!!} NonZero-pi ⟩
  mkratio (1 * p) (1 * q) {{nz'}}
    ≡⟨ cong (λ x → mkratio x (1 * q) {{nz'}}) nat-one-lem ⟩
  mkratio p (1 * q) {{nz'}}
    ≡⟨ {!!} ⟩ 
  mkratio p q {{nz}}
    ≡⟨ {!!} ⟩
  Rational.ratio p q prf
  ∎
  where
  nz' : NonZero (1 * q)
  nz' = transport NonZero (sym nat-one-lem) nz

k-over-k-lem : ∀{k} → suc k :/ suc k ≡ one
k-over-k-lem {k} = {!!} 

zero-over-k-lem : ∀{k} → {{_ : NonZero k}} → zero :/ k ≡ zro
zero-over-k-lem {k} with gcd zero k 
zero-over-k-lem {k} | gcd-res d isGCD with {!!} ofType d ≡ gcd! zero k
... | x = {!!}

common-denom-lem : (p₁ p₂ q : Nat) → {{_ : NonZero q}} → p₁ :/ q + p₂ :/ q ≡ (p₁ + p₂) :/ q
common-denom-lem p₁ p₂ q = {!!}
