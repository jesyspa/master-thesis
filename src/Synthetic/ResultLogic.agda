{-# OPTIONS --type-in-type #-}
module Synthetic.ResultLogic (ST : Set) where

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
  setstate-≡R : ∀{st}(ce : CryptoExpr A)
              → (g : A → ST)
              → ce ≡R[ st ] (ce >>= λ a → Invoke-FM (SetState $ g a) (const $ Return-FM a))

setstate-≡R-gen : ∀{A B st}(ce : CryptoExpr A)
                → (f : A → B)
                → (g : A → ST)
                → fmap f ce ≡R[ st ] (ce >>= λ a → Invoke-FM (SetState $ g a) (const $ Return-FM $ f a))
setstate-≡R-gen (Return-FM a) f g = {!!}
setstate-≡R-gen (Invoke-FM c cont) f g = {!!}

