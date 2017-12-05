module MyPrelude where

open import Prelude.Empty public using()
open import Prelude.Unit public using(Unit; tt)
open import Prelude.Bool public using(Bool; IsTrue; isYes; if_then_else_)
open import Prelude.Sum public using()
open import Prelude.Product public using(_×_; Σ; _,_; fst; snd)
open import Prelude.Function public using(_∘_; _$_; id; const)
open import Prelude.Equality public using(_≡_; refl; Eq; eqReasoningStep; _∎; cong; cong₂; transport; sym; trans)
open import Prelude.Nat public using(Nat; suc; zero; SemiringNat; EqNat; NonZero; _+N_; _*N_)
open import Prelude.Fin public using(Fin; suc; zero; finToNat)
open import Prelude.List public using (List; []; _∷_; [_]; _++_; map; concat; foldr; concatMap; replicate; filter)
open import Numeric.Rational public using(Rational; mkratio; SemiringRational; EqRational; _*Q_)
open import Numeric.Nat.Divide public using(_Divides_; factor)
open import Numeric.Nat.GCD public using(gcd; gcd!; gcd-res; IsGCD; is-gcd; gcd-zero-l)
open import Prelude.Semiring public using(Semiring)

open Semiring {{...}} public
open Eq {{...}} public
open IsGCD {{...}} public

sum : {A : Set} → {{_ : Semiring A}} → List A → A
sum = foldr _+_ zro

fins : ∀{n} → List (Fin (suc n))
fins {zero} =  [ zero ]
fins {suc n} =  zero ∷ map suc fins
