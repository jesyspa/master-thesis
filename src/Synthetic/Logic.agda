{-# OPTIONS --type-in-type #-}
module Synthetic.Logic (ST : Set) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open FM
open import Synthetic.CryptoExpr ST
open import Synthetic.CryptoExprHelpers
open import Synthetic.StateBounds ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions

open CommandStructure

postulate
  _≡E_ : ∀{A} → CryptoExpr A → CryptoExpr A → Set
  refl-≡E : ∀{A}{ce : CryptoExpr A} → ce ≡E ce
  sym-≡E : ∀{A}{ce cf : CryptoExpr A} → ce ≡E cf → cf ≡E ce
  trans-≡E : ∀{A}{ce cf cg : CryptoExpr A} → ce ≡E cf → cf ≡E cg → ce ≡E cg

infixr 0 eqEReasoningStep eqEReasoningStepʳ eqEReasoningStepˡ eqEReasoningStepˡʳ
infixr 1 _∎E

reflˡ-≡E : ∀{A}{ce cf : CryptoExpr A} → ce ≡ cf → ce ≡E cf
reflˡ-≡E refl = refl-≡E

syntax eqEReasoningStep x q p = x ≡E⟨ p ⟩ q
eqEReasoningStep : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → x ≡E y → x ≡E z
x ≡E⟨ p ⟩ q = trans-≡E p q

syntax eqEReasoningStepʳ x q p = x ≡E⟨ p ⟩ʳ q
eqEReasoningStepʳ : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → y ≡E x → x ≡E z
x ≡E⟨ p ⟩ʳ q = trans-≡E (sym-≡E p) q

syntax eqEReasoningStepˡ x q p = x ≡E⟨ p ⟩ˡ q
eqEReasoningStepˡ : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → x ≡ y → x ≡E z
x ≡E⟨ refl ⟩ˡ q = q

syntax eqEReasoningStepˡʳ x q p = x ≡E⟨ p ⟩ˡʳ q
eqEReasoningStepˡʳ : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → y ≡ x → x ≡E z
x ≡E⟨ refl ⟩ˡʳ q = q

_∎E : ∀{A}(ce : CryptoExpr A) → ce ≡E ce
ce ∎E = refl-≡E

postulate
  cong≡E-invoke : ∀{A} c {comt cont : Response CryptoExprCS c → CryptoExpr A}
                → (∀ r → comt r ≡E cont r)
                → Invoke-FM c comt ≡E Invoke-FM c cont
  cong≡E->>=ˡ : ∀{A B}{ce cf : CryptoExpr A}(f : A → CryptoExpr B)
              → ce ≡E cf → (ce >>= f) ≡E (cf >>= f)
  reorder-nowrite-base : ∀{A}(c c′ : Command CryptoExprCS)
                       → NotAWrite c → NotAWrite c′
                       → (cont : Response CryptoExprCS c → Response CryptoExprCS c′ → CryptoExpr A)
                       → Invoke-FM c (λ r → Invoke-FM c′ (cont r)) ≡E Invoke-FM c′ λ r′ → Invoke-FM c (λ r → cont r r′)
  reorder-onewrite-base : ∀{A}(c c′ : Command CryptoExprCS)
                        → NotARead c′ → NotAWrite c′
                        → (cont : Response CryptoExprCS c → Response CryptoExprCS c′ → CryptoExpr A)
                        → Invoke-FM c (λ r → Invoke-FM c′ (cont r)) ≡E Invoke-FM c′ λ r′ → Invoke-FM c (λ r → cont r r′)

  merge-uniform : ∀{A} n k (f : BitVec (n + k) → CryptoExpr A)
                → Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f (vconcat v w))
                  ≡E Invoke-FM (Uniform (n + k)) f
  trivial-uniform : ∀{A n} (ce : CryptoExpr A)
                  → ce ≡E Invoke-FM (Uniform n) (const ce)
  trivial-getstate : ∀{A}(ce : CryptoExpr A)
                   → ce ≡E Invoke-FM GetState (const ce)
  join-getstate : ∀{A}(f : ST → ST → CryptoExpr A)
                → Invoke-FM GetState (λ st → Invoke-FM GetState λ st′ → f st st′)
                  ≡E Invoke-FM GetState (λ st → f st st)
  join-setstate : ∀{A} st st′ (ce : CryptoExpr A)
                → Invoke-FM (SetState st) (const $ Invoke-FM (SetState st′) (const ce))
                  ≡E Invoke-FM (SetState st′) (const ce)
  relate-setget : ∀{A} st (f : ST → CryptoExpr A)
                → Invoke-FM (SetState st) (const $ Invoke-FM GetState f)
                  ≡E Invoke-FM (SetState st) (const $ f st)
  relate-getset : ∀{A}(f : ST → CryptoExpr A)
                → Invoke-FM GetState (λ st → Invoke-FM (SetState st) (const $ f st))
                  ≡E Invoke-FM GetState f
