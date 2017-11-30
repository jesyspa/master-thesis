module RationalLemmas where

open import MyPrelude
open import NatLemmas

rat-one-def : one ≡ Rational.ratio 1 1 {{tt}} refl
rat-one-def = refl

rat-one-lem-try2 : {x : Rational} → one * x ≡ x
rat-one-lem-try2 {Rational.ratio p q {{nz}} prf} with one * Rational.ratio p q prf
... | Rational.ratio p2 q2 {{nz'}} prf' =
  {!!}
    ≡⟨ {!!} ⟩
  {!!}
  ∎

rat-one-lem : {x : Rational} → one * x ≡ x
rat-one-lem {Rational.ratio p q {{nz}} prf} = 
  mkratio 1 1 * Rational.ratio p q prf
    ≡⟨ refl ⟩
  Rational.ratio 1 1 refl * Rational.ratio p q prf
    ≡⟨ refl ⟩
  mkratio (1 * p) (1 * q) {{{!!}}} 
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ refl ⟩
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
