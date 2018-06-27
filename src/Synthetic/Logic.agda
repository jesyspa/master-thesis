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

  reorder-nowrite-base : ∀{A}(c c′ : Command CryptoExprCS)
                       → NotAWrite c → NotAWrite c′
                       → (cont : Response CryptoExprCS c → Response CryptoExprCS c′ → CryptoExpr A)
                       → Invoke-FM c (λ r → Invoke-FM c′ (cont r)) ≡E Invoke-FM c′ λ r′ → Invoke-FM c (λ r → cont r r′)
  reorder-onewrite-base : ∀{A}(c c′ : Command CryptoExprCS)
                        → NotARead c′ → NotAWrite c′
                        → (cont : Response CryptoExprCS c → Response CryptoExprCS c′ → CryptoExpr A)
                        → Invoke-FM c (λ r → Invoke-FM c′ (cont r)) ≡E Invoke-FM c′ λ r′ → Invoke-FM c (λ r → cont r r′)

reorder-nowrite-lem : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                     → NotAWrite c → NoWrites ce
                     → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                     → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-nowrite-lem c (Return-FM a) naw nw ct = refl-≡E
reorder-nowrite-lem c (Invoke-FM c′   cont) naw (Invoke-NW _ naw′ nct) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-nowrite-base c c′ naw naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-nowrite-lem c (cont r′) naw (nct r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-lemˡ : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NotARead c → NotAWrite c
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-lemˡ c (Return-FM a) nar naw ct = refl-≡E
reorder-onewrite-lemˡ c (Invoke-FM c′ cont) nar naw ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c′ c nar naw (λ r′ r → cont r′ >>= λ a → ct a r) ⟩ʳ
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-lemˡ c (cont r′) nar naw ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-lemʳ : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NoReads ce → NoWrites ce
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-lemʳ c (Return-FM a) nr nw ct = refl-≡E
reorder-onewrite-lemʳ c (Invoke-FM c′ cont) (Invoke-NR _ nar′ ncr) (Invoke-NW _ naw′ ncw) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c c′ nar′ naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-lemʳ c (cont r′) (ncr r′) (ncw r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-lem : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NoReads ce → NoWrites ce
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-lem c (Return-FM a) nr nw ct = refl-≡E
reorder-onewrite-lem c (Invoke-FM c′ cont) (Invoke-NR _ nar′ ncr) (Invoke-NW _ naw′ ncw) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c c′ nar′ naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-lem c (cont r′) (ncr r′) (ncw r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-nowrite : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                → (f : A → B → CryptoExpr C)
                → NoWrites ce → NoWrites cf
                → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-nowrite ce (Return-FM a) f ne _ = refl-≡E
reorder-nowrite ce (Invoke-FM c′ cont) f naw (Invoke-NW _ nav ncont) =
  (ce >>= λ a → Invoke-FM c′ λ r′ → cont r′ >>= f a)
    ≡E⟨ (reorder-nowrite-lem c′ ce nav naw λ a r′ → cont r′ >>= f a) ⟩ʳ
  (Invoke-FM c′ λ r′ → ce >>= λ a → cont r′ >>= λ b → f a b)
    ≡E⟨ congE-invoke _ _ _ (λ r′ → reorder-nowrite ce (cont r′) f naw (ncont r′)) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ b → ce >>= λ a → f a b)
  ∎E

  
reorder-onewriteˡ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites cf → NoReads cf
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteˡ ce (Return-FM x) f nw nr = refl-≡E
reorder-onewriteˡ ce (Invoke-FM c′ cont)   f (Invoke-NW _ naw cnw) (Invoke-NR _ nar cnr) =
  (ce >>= λ a → Invoke-FM c′ λ r′ → cont r′ >>= f a)
    ≡E⟨ (reorder-onewrite-lemˡ c′ ce nar naw λ a r′ → cont r′ >>= f a) ⟩ʳ
  (Invoke-FM c′ λ r′ → ce >>= λ a → cont r′ >>= f a)
    ≡E⟨ congE-invoke _ _ _ (λ r′ → reorder-onewriteˡ ce (cont r′) f (cnw r′) (cnr r′)) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ b → ce >>= λ a → f a b)
  ∎E

reorder-onewriteʳ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites ce → NoReads ce
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteʳ ce cf f nw nr = sym-≡E $ reorder-onewriteˡ cf ce (flip f) nw nr


postulate
  merge-uniform : ∀{A} n k (f : BitVec (n + k) → CryptoExpr A)
                → Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f (vconcat v w))
                  ≡E Invoke-FM (Uniform (n + k)) f
  unmerge-uniform : ∀{A} n k (f : BitVec n → BitVec k → CryptoExpr A)
                  → Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f v w)
                    ≡E Invoke-FM (Uniform (n + k)) (λ v → let l , r = vsplit n v in f l r)
  trivial-uniform : ∀{A n} (ce : CryptoExpr A)
                  → Invoke-FM (Uniform n) (const ce) ≡E ce
  -- This can probably be derived from the above.
  extend-uniform : ∀{A} n k (f : BitVec n → CryptoExpr A)
                 → Invoke-FM (Uniform (n + k)) (λ v → f (vtake n v)) ≡E Invoke-FM (Uniform n) f
  extend-uniform′ : ∀{A} n k (pf : n ≤ k) (f : BitVec n → CryptoExpr A)
                  → Invoke-FM (Uniform k) (λ v → f (vtake′ n pf v)) ≡E Invoke-FM (Uniform n) f

  trivial-getstate : ∀{A}(ce : CryptoExpr A)
                   → Invoke-FM GetState (const ce) ≡E ce
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