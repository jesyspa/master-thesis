{-# OPTIONS --type-in-type #-}
module Synthetic.Logic (ST : Set) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Synthetic.CryptoExpr ST
open import Synthetic.StateBounds ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions

open CommandStructure

postulate
  _≡E_ : ∀{A} → CryptoExpr A → CryptoExpr A → Set
  refl-≡E : ∀{A}{ce : CryptoExpr A} → ce ≡E ce
  sym-≡E : ∀{A}{ce cf : CryptoExpr A} → ce ≡E cf → cf ≡E ce
  trans-≡E : ∀{A}{ce cf cg : CryptoExpr A} → ce ≡E cf → cf ≡E cg → ce ≡E cg

infixr 0 eqEReasoningStep eqEReasoningStepʳ eqEReasoningStepˡ
infixr 1 _∎E

syntax eqEReasoningStep x q p = x ≡E⟨ p ⟩ q
eqEReasoningStep : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → x ≡E y → x ≡E z
x ≡E⟨ p ⟩ q = trans-≡E p q

syntax eqEReasoningStepˡ x q p = x ≡E⟨ p ⟩ˡ q
eqEReasoningStepˡ : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → x ≡ y → x ≡E z
x ≡E⟨ refl ⟩ˡ q = q

syntax eqEReasoningStepʳ x q p = x ≡E⟨ p ⟩ʳ q
eqEReasoningStepʳ : ∀{A}(x : CryptoExpr A){y z} → y ≡E z → y ≡E x → x ≡E z
x ≡E⟨ p ⟩ʳ q = trans-≡E (sym-≡E p) q

_∎E : ∀{A}(ce : CryptoExpr A) → ce ≡E ce
ce ∎E = refl-≡E

postulate
  congE-invoke : ∀{A} c (comt cont : Response CryptoExprCS c → CryptoExpr A)
               → (∀ r → comt r ≡E cont r)
               → Invoke-FM c comt ≡E Invoke-FM c cont
  congE->>=ˡ : ∀{A B}(ce cf : CryptoExpr A)(f : A → CryptoExpr B)
             → ce ≡E cf → (ce >>= f) ≡E (cf >>= f)
  congE->>=ʳ : ∀{A B}(ce : CryptoExpr A)(f g : A → CryptoExpr B)
             → (∀ a → f a ≡E g a) → (ce >>= f) ≡E (ce >>= g)

  non-trivial : _≡E_ {Bool} (return true) (return false) → ⊥

  reorder-uniform : ∀{A B} n (ce : CryptoExpr A)
                  → (cont : A → BitVec n → CryptoExpr B)
                  → (ce >>= λ a → Invoke-FM (Uniform n) (cont a)) ≡E Invoke-FM (Uniform n) λ v → ce >>= λ a → cont a v
  reorder-getstate : ∀{A B} (ce : CryptoExpr A)
                   → (cont : A → ST → CryptoExpr B)
                   → NoWrites ce
                   → (ce >>= λ a → Invoke-FM GetState (cont a)) ≡E Invoke-FM GetState λ v → ce >>= λ a → cont a v
  reorder-setstate : ∀{A B} st (ce : CryptoExpr A)
                   → (cont : A → CryptoExpr B)
                   → NoReads ce → NoWrites ce
                   → (ce >>= λ a → Invoke-FM (SetState st) (const (cont a))) ≡E Invoke-FM (SetState st) (const $ ce >>= cont)


reorder-nowrite : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                → (f : A → B → CryptoExpr C)
                → NoWrites ce → NoWrites cf
                → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-nowrite ce (Return-FM a) f ne _ = refl-≡E
reorder-nowrite ce (Invoke-FM (Uniform n) cont) f ne (Uniform-NW _ _ ncont) =
  (ce >>= λ a → Invoke-FM (Uniform n) λ v → cont v >>= f a)
    ≡E⟨ reorder-uniform n ce (λ a v → cont v >>= f a) ⟩
  (Invoke-FM (Uniform n) λ v → ce >>= λ a → cont v >>= λ b → f a b)
    ≡E⟨ congE-invoke _ _ _ (λ v → reorder-nowrite ce (cont v) f ne (ncont v)) ⟩
  (Invoke-FM (Uniform n) λ v → cont v >>= λ b → ce >>= λ a → f a b)
  ∎E
reorder-nowrite ce (Invoke-FM GetState cont) f ne (GetState-NW _ ncont) =
  (ce >>= λ a → Invoke-FM GetState λ st → cont st >>= f a)
    ≡E⟨ reorder-getstate _ _ ne ⟩
  (Invoke-FM GetState λ st → ce >>= λ a → cont st >>= λ b → f a b)
    ≡E⟨ congE-invoke _ _ _ (λ st → reorder-nowrite ce (cont st) f ne (ncont st)) ⟩
  (Invoke-FM GetState λ st → cont st >>= λ b → ce >>= λ a → f a b)
  ∎E
reorder-nowrite ce (Invoke-FM (SetState x) cont) f ne ()

  
reorder-onewriteˡ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites cf → NoReads cf
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteˡ ce (Return-FM x) f nw nr = refl-≡E
reorder-onewriteˡ ce (Invoke-FM (Uniform n) cont)   f (Uniform-NW _ _ cnw) (Uniform-NR _ _ cnr) =
  (ce >>= λ a → Invoke-FM (Uniform n) λ v → cont v >>= f a)
    ≡E⟨ reorder-uniform n ce (λ a v → cont v >>= f a) ⟩
  (Invoke-FM (Uniform n) λ v → ce >>= λ a → cont v >>= f a)
    ≡E⟨ congE-invoke _ _ _ (λ v → reorder-onewriteˡ ce (cont v) f (cnw v) (cnr v)) ⟩
  (Invoke-FM (Uniform n) λ v → cont v >>= λ b → ce >>= λ a → f a b)
  ∎E
reorder-onewriteˡ ce (Invoke-FM  GetState cont)     f nw () 
reorder-onewriteˡ ce (Invoke-FM (SetState st) cont) f () nr

reorder-onewriteʳ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites ce → NoReads ce
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteʳ ce cf f nw nr = sym-≡E $ reorder-onewriteˡ cf ce (flip f) nw nr


postulate
  merge-uniform : ∀{A} n k (f : BitVec (n + k) → CryptoExpr A)
                → Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f (vconcat v w))
                  ≡E Invoke-FM (Uniform (n + k)) f
  extend-uniform : ∀{A} n k (f : BitVec n → CryptoExpr A)
                 → Invoke-FM (Uniform (n + k)) (λ v → f (vtake n v)) ≡E Invoke-FM (Uniform n) f

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
