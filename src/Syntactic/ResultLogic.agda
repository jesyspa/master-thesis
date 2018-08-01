{-# OPTIONS --type-in-type #-}
module Syntactic.ResultLogic (ST : Set) where

open import ThesisPrelude
open import Syntactic.Enumeration
open import Syntactic.CommandStructure
open FM
open import Syntactic.CryptoExpr ST
open import Syntactic.CryptoExprHelpers
open import Syntactic.StateBounds ST
open import Syntactic.Logic ST
open import Syntactic.LogicDerived ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions
open import Utility.Vector.Props
open import Utility.Num

open CommandStructure


syntax result-ind st ce cf = ce ≡R[ st ] cf
data result-ind {A} : ST → CryptoExpr A → CryptoExpr A → Set where
  embed-≡R : ∀{st}{ce cf : CryptoExpr A} → ce ≡E cf → ce ≡R[ st ] cf
  sym-≡R : ∀{st}{ce cf : CryptoExpr A} → ce ≡R[ st ] cf → cf ≡R[ st ] ce
  trans-≡R : ∀{st}{ce cf cg : CryptoExpr A} → ce ≡R[ st ] cf → cf ≡R[ st ] cg → ce ≡R[ st ] cg
  cong≡R-invoke : ∀{st} c {comt cont : Response CryptoExprCS c → CryptoExpr A}
                → NotAWrite c → NotARead c
                → (∀ r → comt r ≡R[ st ] cont r)
                → Invoke-FM c comt ≡R[ st ] Invoke-FM c cont

  getstate-≡R : ∀{st}(cont : ST → CryptoExpr A) 
              → cont st ≡R[ st ] Invoke-FM GetState cont
  setstate-≡R : ∀{st}(ce : CryptoExpr A)(cf : CryptoExpr ⊤)
              → (g : A → ST)
              → ce ≡R[ st ] (ce >>= λ a → cf >> Return-FM a)

infixr 0 eqRReasoningStep eqRReasoningStepʳ eqRReasoningStepˡ eqRReasoningStepˡʳ
infixr 1 _∎R

reflˡ-≡R : ∀{A st}{ce cf : CryptoExpr A} → ce ≡ cf → ce ≡R[ st ] cf
reflˡ-≡R refl = embed-≡R refl-≡E 

syntax eqRReasoningStep  x q p = x ≡R⟨ p ⟩ q
eqRReasoningStep : ∀{A st} (x : CryptoExpr A){y z} → y ≡R[ st ] z → x ≡R[ st ] y → x ≡R[ st ] z
x ≡R⟨ p ⟩ q = trans-≡R p q

syntax eqRReasoningStepʳ  x q p = x ≡R⟨ p ⟩ʳ q
eqRReasoningStepʳ : ∀{A st} (x : CryptoExpr A){y z} → y ≡R[ st ] z → y ≡R[ st ] x → x ≡R[ st ] z
x ≡R⟨ p ⟩ʳ q = trans-≡R (sym-≡R p) q

syntax eqRReasoningStepˡ  x q p = x ≡R⟨ p ⟩ˡ q
eqRReasoningStepˡ : ∀{A st} (x : CryptoExpr A){y z} → y ≡R[ st ] z → x ≡ y → x ≡R[ st ] z
x ≡R⟨ refl ⟩ˡ q = q

syntax eqRReasoningStepˡʳ x q p = x ≡R⟨ p ⟩ˡʳ q
eqRReasoningStepˡʳ : ∀{A st} (x : CryptoExpr A){y z} → y ≡R[ st ] z → y ≡ x → x ≡R[ st ] z
x ≡R⟨ refl ⟩ˡʳ q = q

_∎R : ∀{A st}(ce : CryptoExpr A) → ce ≡R[ st ] ce
ce ∎R = reflˡ-≡R refl

cong≡R->>=ʳ : ∀{A B st}(ce : CryptoExpr A){f g : A → CryptoExpr B}
            → NoWrites ce → NoReads ce
            → (∀ a → f a ≡R[ st ] g a)
            → (ce >>= f) ≡R[ st ] (ce >>= g)
cong≡R->>=ʳ (Return-FM a) nw nr eq = eq a
cong≡R->>=ʳ (Invoke-FM c cont) (Invoke-NW .c naw nw) (Invoke-NR .c nar nr) eq
  = cong≡R-invoke c naw nar λ r → cong≡R->>=ʳ (cont r) (nw r) (nr r) eq

fmap≡R-cong : ∀{A B st}{ce cf : CryptoExpr A}(f : A → B)
            → ce ≡R[ st ] cf → fmap f ce ≡R[ st ] fmap f cf
fmap≡R-cong f (embed-≡R eq) = embed-≡R $ cong≡E-fmap f eq
fmap≡R-cong f (sym-≡R eq) = sym-≡R $ fmap≡R-cong f eq
fmap≡R-cong f (trans-≡R eq ep) = trans-≡R (fmap≡R-cong f eq) (fmap≡R-cong f ep)
fmap≡R-cong f (cong≡R-invoke c naw nar eq) = cong≡R-invoke c naw nar λ r → fmap≡R-cong f (eq r)
fmap≡R-cong f (getstate-≡R cont) = getstate-≡R λ r → fmap f (cont r) 
fmap≡R-cong f (setstate-≡R ce cf g) = {!setstate-≡R ? ? ?!}


setstate-≡R-gen : ∀{A B C st}(ce : CryptoExpr A)(f : A → CryptoExpr B)(g : A → C)
                → fmap g ce ≡R[ st ] (ce >>= λ a → f a >> return (g a))
setstate-≡R-gen ce f g =
  fmap g ce
    ≡R⟨ {!!} ⟩
  fmap g (ce >>= λ a → (f a >> return ⊤) >> return a)
    ≡R⟨ unsafeEqual ⟩ˡ -- monad law
  ((ce >>= λ a → (f a >> return ⊤) >> return a) >>= λ a′ → return (g a′))
    ≡R⟨ unsafeEqual ⟩ˡ -- monad law
  (ce >>= λ a → (f a >> return ⊤) >> return a >>= λ a′ → return (g a′))
    ≡R⟨ unsafeEqual ⟩ˡ -- monad law
  (ce >>= λ a → (f a >> return ⊤) >> return (g a))
    ≡R⟨ unsafeEqual ⟩ˡ -- monad law
  (ce >>= λ a → f a >> (return ⊤ >> return (g a)))
    ≡R⟨ unsafeEqual ⟩ˡ -- monad law
  (ce >>= λ a → f a >> return (g a))
  ∎R
  where open import Prelude.Equality.Unsafe

