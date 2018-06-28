{-# OPTIONS --type-in-type #-}
module Synthetic.LogicDerived (ST : Set) where

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
open import Utility.Vector.Props
open import Utility.Num

open CommandStructure

cong≡E->>=ʳ : ∀{A B}(ce : CryptoExpr A){f g : A → CryptoExpr B}
            → (∀ a → f a ≡E g a) → (ce >>= f) ≡E (ce >>= g)
cong≡E->>=ʳ (Return-FM a) eq = eq a
cong≡E->>=ʳ (Invoke-FM c cont) eq = cong≡E-invoke c λ r → cong≡E->>=ʳ (cont r) eq

reorder-nowrite-lem : ∀{A B}(c : Command CryptoExprCS)(ce : CryptoExpr A)
                     → NotAWrite c → NoWrites ce
                     → (cont : A → Response CryptoExprCS c → CryptoExpr B)
                     → (Invoke-FM c λ r → ce >>= λ a → cont a r) ≡E (ce >>= λ a → Invoke-FM c (cont a))
reorder-nowrite-lem c (Return-FM a) naw nw ct = refl-≡E
reorder-nowrite-lem c (Invoke-FM c′   cont) naw (Invoke-NW _ naw′ nct) ct =
  (Invoke-FM c λ r → Invoke-FM c′ λ r′ → cont r′ >>= λ a → ct a r)
    ≡E⟨ reorder-nowrite-base c c′ naw naw′ (λ r r′ → cont r′ >>= λ a → ct a r) ⟩
  (Invoke-FM c′ λ r′ → Invoke-FM c λ r → cont r′ >>= λ a → ct a r)
    ≡E⟨ (cong≡E-invoke _ λ r′ → reorder-nowrite-lem c (cont r′) naw (nct r′) ct) ⟩
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
    ≡E⟨ (cong≡E-invoke _ λ r′ → reorder-onewrite-lemˡ c (cont r′) nar naw ct) ⟩
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
    ≡E⟨ (cong≡E-invoke _ λ r′ → reorder-onewrite-lemʳ c (cont r′) (ncr r′) (ncw r′) ct) ⟩
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
    ≡E⟨ (cong≡E-invoke _ λ r′ → reorder-onewrite-lem c (cont r′) (ncr r′) (ncw r′) ct) ⟩
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
    ≡E⟨ cong≡E-invoke _ (λ r′ → reorder-nowrite ce (cont r′) f naw (ncont r′)) ⟩
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
    ≡E⟨ cong≡E-invoke _ (λ r′ → reorder-onewriteˡ ce (cont r′) f (cnw r′) (cnr r′)) ⟩
  (Invoke-FM c′ λ r′ → cont r′ >>= λ b → ce >>= λ a → f a b)
  ∎E

reorder-onewriteʳ : ∀{A B C}(ce : CryptoExpr A)(cf : CryptoExpr B)
                  → (f : A → B → CryptoExpr C)
                  → NoWrites ce → NoReads ce
                  → (ce >>= λ a → cf >>= λ b → f a b) ≡E (cf >>= λ b → ce >>= λ a → f a b)
reorder-onewriteʳ ce cf f nw nr = sym-≡E $ reorder-onewriteˡ cf ce (flip f) nw nr

unmerge-uniform : ∀{A} n k (f : BitVec n → BitVec k → CryptoExpr A)
                → Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f v w)
                  ≡E Invoke-FM (Uniform (n + k)) (λ v → let l , r = vsplit n v in f l r)
unmerge-uniform n k f =
  Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → f v w)
    ≡E⟨ (cong≡E-invoke _ λ v → cong≡E-invoke _ λ w → reflˡ-≡E (cong₂ f (vsplit-vconcat-invˡ _ _) (vsplit-vconcat-invʳ v w))) ⟩
  Invoke-FM (Uniform n) (λ v → Invoke-FM (Uniform k) λ w → let l , r = vsplit n (vconcat v w) in f l r)
    ≡E⟨ merge-uniform _ _ _ ⟩
  Invoke-FM (Uniform (n + k)) (λ v → let l , r = vsplit n v in f l r)
  ∎E

extend-uniform : ∀{A} n k (f : BitVec n → CryptoExpr A)
               → Invoke-FM (Uniform n) f ≡E Invoke-FM (Uniform (n + k)) (λ v → f (vtake n v))
extend-uniform n k f =
  (Invoke-FM (Uniform n) λ v → f v)
    ≡E⟨ (cong≡E-invoke _ λ v → trivial-uniform _) ⟩
  (Invoke-FM (Uniform n) λ v → Invoke-FM (Uniform k) λ w → f v)
    ≡E⟨ cong≡E-invoke _ (λ v → cong≡E-invoke _ λ w → reflˡ-≡E $ cong f $ vtake-vconcat-inv v w) ⟩
  (Invoke-FM (Uniform n) λ v → Invoke-FM (Uniform k) λ w → f (vtake n (vconcat v w)))
    ≡E⟨ merge-uniform _ _ _ ⟩
  (Invoke-FM (Uniform (n + k)) λ v → f (vtake n v))
  ∎E
extend-uniform′ : ∀{A}{n k} (pf : n ≤ k) (f : BitVec n → CryptoExpr A)
                → Invoke-FM (Uniform n) f ≡E Invoke-FM (Uniform k) (λ v → f (vtake′ n pf v))
extend-uniform′ {n = n} {k} (diff i eq) f = helper
  where k-is-n+i : k ≡ n + i
        k-is-n+i = suc-Inj eq ⟨≡⟩ auto
        helper : Invoke-FM (Uniform n) f ≡E Invoke-FM (Uniform k) (λ v → f (vtake′ n (diff i eq) v))
        helper rewrite k-is-n+i = extend-uniform _ _ _
