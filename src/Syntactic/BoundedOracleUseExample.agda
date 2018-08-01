{-# OPTIONS --type-in-type #-}
module Syntactic.BoundedOracleUseExample where

open import ThesisPrelude
open import Syntactic.Enumeration
open import Utility.Vector.Definition
open import Utility.Vector.BitVec
open import Utility.List.Elem.Definition

open Enumeration

open import Syntactic.CommandStructure
open import Syntactic.CryptoExpr
open import Syntactic.BoundedOracleUse

instance
  EnumerationBitVec : ∀ n → Enumeration (BitVec n)
  Enumerate         (EnumerationBitVec n) = all-bitvecs n
  EnumerateComplete (EnumerationBitVec n) = all-bitvecs-complete
  EnumerateUnique   (EnumerationBitVec n) p q = all-bitvecs-unique _ p ⟨≡⟩ʳ all-bitvecs-unique _ q
     
  Enumeration⊤ : Enumeration ⊤
  Enumerate         Enumeration⊤ = tt ∷ []
  EnumerateComplete Enumeration⊤ tt = here tt []
  EnumerateUnique Enumeration⊤ (here .unit .[]) (here .unit .[]) = refl
  EnumerateUnique Enumeration⊤ (here .unit .[]) (there .unit .unit .[] ())
  EnumerateUnique Enumeration⊤ (there x .unit .[] ()) q
     
instance
  MonadCryptoExpr : Monad CryptoExpr
  MonadCryptoExpr = MonadFM 

expr : CryptoExpr ⊤
expr = do
  v <- uniform-CE 4
  return tt
     
expr-is-BOU : BoundedOracleUse false zero expr
expr-is-BOU = check-BOU-Sound false zero expr true
