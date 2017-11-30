module MyPrelude where

open import Prelude.Unit public using(Unit; tt)
open import Prelude.Empty public using()
open import Prelude.Sum public using()
open import Prelude.Product public using(_×_; _,_)
open import Prelude.Function public using(_∘_; _$_; id)
open import Prelude.Equality public using(_≡_; refl; eqReasoningStep; _∎; cong; cong₂; transport; sym; trans)
open import Prelude.Nat public using(Nat; suc; zero; SemiringNat; NonZero; _+N_; _*N_)
open import Prelude.List public using (List; []; _∷_; [_]; _++_; map; concat; concatMap)
open import Numeric.Rational public using(Rational; mkratio; SemiringRational; _*Q_)
open import Prelude.Semiring public using(Semiring)

open Semiring {{...}} public
