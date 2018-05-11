module ThesisPrelude where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

open import Prelude.Empty public
open import Prelude.Unit public
open import Prelude.Bool public
open import Prelude.Sum public
open import Prelude.Product public
open import Prelude.Function public
open import Prelude.Equality public
open import Prelude.Decidable public
open import Prelude.Ord public
open import Prelude.Nat public
open import Prelude.Fin public
open import Prelude.List public
open import Prelude.Vec public
open import Prelude.Semiring public
open import Prelude.Monoid public
open import Prelude.Functor public
open import Prelude.Applicative public
open import Prelude.Monad public
open import Prelude.Equality.Inspect public
open import Prelude.Strict public 
open import Tactic.Nat public

eq-as : ∀{l} (A : Set l) (x y : A) → Set l
eq-as _ = _≡_

syntax eq-as A x y = x ≡ y as A

infixr 2 _⊎_
_⊎_ : ∀{l} → Set l → Set l → Set l
_⊎_ = Either

