{-# OPTIONS --type-in-type #-}
open import Probability.Class
open import Probability.PropsClass
open import Synthetic.Enumeration
module Synthetic.EpsilonLogic (ST Q : Set){{PQ : Probability Q}}{{EST : Enumeration ST}} where

open import ThesisPrelude
open import Synthetic.CommandStructure
open FM
open import Synthetic.EnumerationInstances
open import Synthetic.CryptoExpr ST
open import Synthetic.CryptoExprHelpers
open import Synthetic.StateBounds ST
open import Synthetic.Logic ST
open import Utility.Vector.Definition
open import Utility.Vector.Functions

open CommandStructure
open Enumeration {{...}}

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

_∎≈E : ∀{A}(ce : CryptoExpr A) → ce ≈E[ zro ] ce
ce ∎≈E = refl-≈E

ResponseEnumeration : ∀ c → Enumeration (Response CryptoExprCS c)
ResponseEnumeration (Uniform n)   = it
ResponseEnumeration  GetState     = it
ResponseEnumeration (SetState st) = it

postulate
  cong≈E-invoke : ∀{A q} c {comt cont : Response CryptoExprCS c → CryptoExpr A}
                → (∀ r → comt r ≈E[ q ] cont r)
                → Invoke-FM c comt ≈E[ q ] Invoke-FM c cont

  cong≈E->>=ˡ : ∀{A B q}(ce cf : CryptoExpr A)(f : A → CryptoExpr B)
              → ce ≈E[ q ] cf → (ce >>= f) ≈E[ q ] (cf >>= f)

cong≈E->>=ʳ : ∀{A B q}(ce : CryptoExpr A)(f g : A → CryptoExpr B)
            → (∀ a → f a ≈E[ q ] g a) → (ce >>= f) ≈E[ q ] (ce >>= g)
cong≈E->>=ʳ (Return-FM a) f g pf = pf a
cong≈E->>=ʳ (Invoke-FM c cont) f g pf = cong≈E-invoke c λ r → cong≈E->>=ʳ (cont r) f g pf


postulate
  uniform-diff : ∀{A n}(comt cont : BitVec n → CryptoExpr A)
               → (εf : BitVec n → Q) → (ε : Q)
               → (∀ v → comt v ≈E[ εf v ] cont v)
               → sum (map εf Enumerate) ≤ ε
               → Invoke-FM (Uniform n) comt ≈E[ ε ] Invoke-FM (Uniform n) cont
