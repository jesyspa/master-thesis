{-# OPTIONS --type-in-type #-}
open import Probability.Class
open import Probability.PropsClass
module Synthetic.EpsilonLogic (ST Q : Set){{PQ : Probability Q}} where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open FM
open import Synthetic.CryptoExpr ST
open import Synthetic.CryptoExprHelpers
open import Synthetic.StateBounds ST
open import Synthetic.Logic ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions

open CommandStructure

syntax approx-eq ε ce cf = ce ≈E[ ε ] cf
postulate
  approx-eq : ∀{A} → Q → CryptoExpr A → CryptoExpr A → Set
  -- TODO: Add non-negativity.
  embed-eq : ∀{A}{q : Q}{ce cf : CryptoExpr A} → ce ≡E cf → ce ≈E[ q ] cf
  sym-≈E : ∀{A}{q : Q}{ce cf : CryptoExpr A} → ce ≈E[ q ] cf → cf ≈E[ q ] ce
  trans-≈E : ∀{A}{q p : Q}{ce cf cg : CryptoExpr A} → ce ≈E[ q ] cf → cf ≈E[ p ] cg → ce ≈E[ q + p ] cg
  weaken-≈E : ∀{A}{q p : Q}{ce cf : CryptoExpr A} → ce ≈E[ q ] cf → q ≤ p → ce ≈E[ p ] cf

refl-≈E : ∀{A}{q : Q}{ce : CryptoExpr A} → ce ≈E[ q ] ce
refl-≈E = embed-eq refl-≡E

infixr 0 ≈EReasoningStep ≈EReasoningStepʳ ≈EReasoningStepˡ ≈EApprox
infixr 1 _∎≈E

syntax ≈EReasoningStep x qf pf = x ≈E⟨ pf ⟩ qf
≈EReasoningStep : ∀{A}{q p}(x : CryptoExpr A){y z} → y ≈E[ q ] z → x ≈E[ p ] y → x ≈E[ p + q ] z
x ≈E⟨ pf ⟩ qf = trans-≈E pf qf

syntax ≈EReasoningStepˡ x qf pf = x ≈E⟨ pf ⟩ˡ qf
≈EReasoningStepˡ : ∀{A}{q}(x : CryptoExpr A){y z} → y ≈E[ q ] z → x ≡ y → x ≈E[ q ] z
x ≈E⟨ refl ⟩ˡ qf = qf

syntax ≈EReasoningStepʳ x qf pf = x ≈E⟨ pf ⟩ʳ qf
≈EReasoningStepʳ : ∀{A}{q p}(x : CryptoExpr A){y z} → y ≈E[ q ] z → y ≈E[ p ] x → x ≈E[ p + q ] z
x ≈E⟨ pf ⟩ʳ qf = trans-≈E (sym-≈E pf) qf

syntax ≈EApprox x qf le = x ≈E⟨ le ⟩ᵃ qf
≈EApprox : ∀{A}{q p}(x : CryptoExpr A){y} → x ≈E[ q ] y → q ≤ p → x ≈E[ p ] y
x ≈E⟨ le ⟩ᵃ qf = weaken-≈E qf le

_∎≈E : ∀{A}(ce : CryptoExpr A) → ce ≡E ce
ce ∎≈E = refl-≡E

{-

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

reorder-nowrite-unit : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                     → NotAWrite c → NoWrites ce
                     → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                     → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-nowrite-unit c (Return-FM a) naw nw ct = refl-≡E
reorder-nowrite-unit c (Invoke-FM c′   cont) naw (Invoke-NW _ naw′ nct) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-nowrite-base c c′ naw naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-nowrite-unit c (cont r′) naw (nct r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-unitˡ : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NotARead c → NotAWrite c
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-unitˡ c (Return-FM a) nar naw ct = refl-≡E
reorder-onewrite-unitˡ c (Invoke-FM c′ cont) nar naw ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c′ c nar naw (λ r′ r → cont r′ >>= λ a → ct a r) ⟩ʳ
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-unitˡ c (cont r′) nar naw ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-unitʳ : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NoReads ce → NoWrites ce
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-unitʳ c (Return-FM a) nr nw ct = refl-≡E
reorder-onewrite-unitʳ c (Invoke-FM c′ cont) (Invoke-NR _ nar′ ncr) (Invoke-NW _ naw′ ncw) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c c′ nar′ naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-unitʳ c (cont r′) (ncr r′) (ncw r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E

reorder-onewrite-unit : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                      → NoReads ce → NoWrites ce
                      → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                      → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-onewrite-unit c (Return-FM a) nr nw ct = refl-≡E
reorder-onewrite-unit c (Invoke-FM c′ cont) (Invoke-NR _ nar′ ncr) (Invoke-NW _ naw′ ncw) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-onewrite-base c c′ nar′ naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (congE-invoke _ _ _ λ r′ → reorder-onewrite-unit c (cont r′) (ncr r′) (ncw r′) ct) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ a → Invoke-FM c (ct a))
  ∎E
postulate
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
reorder-nowrite ce (Invoke-FM c′ cont) f ne (Invoke-NW _ _ ncont) =
  (ce >>= λ a → Invoke-FM c′ λ r′ → cont r′ >>= f a)
    ≡E⟨ {! reorder-uniform n ce (λ a v → cont v >>= f a) !} ⟩
  (Invoke-FM c′ λ r′ → ce >>= λ a → cont r′ >>= λ b → f a b)
    ≡E⟨ congE-invoke _ _ _ (λ r′ → reorder-nowrite ce (cont r′) f ne (ncont r′)) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ b → ce >>= λ a → f a b)
  ∎E

  
reorder-onewriteˡ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites cf → NoReads cf
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteˡ ce (Return-FM x) f nw nr = refl-≡E
reorder-onewriteˡ ce (Invoke-FM c′ cont)   f (Invoke-NW _ _ cnw) (Invoke-NR _ _ cnr) =
  (ce >>= λ a → Invoke-FM c′ λ r′ → cont r′ >>= f a)
    ≡E⟨ {! reorder-uniform n ce (λ a v → cont v >>= f a )!} ⟩
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

-}
