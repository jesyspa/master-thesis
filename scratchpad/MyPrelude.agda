module MyPrelude where

open import Prelude.Empty public using()
open import Prelude.Unit public using(Unit; tt)
open import Prelude.Bool public using(IsTrue; isYes)
open import Prelude.Sum public using()
open import Prelude.Product public using(_×_; _,_; fst; snd)
open import Prelude.Function public using(_∘_; _$_; id)
open import Prelude.Equality public using(_≡_; refl; Eq; eqReasoningStep; _∎; cong; cong₂; transport; sym; trans)
open import Prelude.Nat public using(Nat; suc; zero; SemiringNat; NonZero; _+N_; _*N_)
open import Prelude.Fin public using(Fin; suc; zero)
open import Prelude.List public using (List; []; _∷_; [_]; _++_; map; concat; foldr; concatMap; replicate)
open import Numeric.Rational public using(Rational; mkratio; SemiringRational; EqRational; _*Q_)
open import Prelude.Semiring public using(Semiring)

open Semiring {{...}} public
open Eq {{...}} public
