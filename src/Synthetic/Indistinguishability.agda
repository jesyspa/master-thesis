open import Synthetic.CryptoState
module Synthetic.Indistinguishability (CS : CryptoState) where

open import ThesisPrelude
open import Synthetic.Enumeration
open import Synthetic.CommandStructure
open import Synthetic.CryptoExpr CS
open import Synthetic.Interpretation CS
open import Utility.Vector.Definition
open import Probability.Class
  
postulate
  _≡D_ : ∀{A}{{_ : Eq A}} → M A → M A → Set
  refl-≡D : ∀{A}{{_ : Eq A}}(m : M A) → m ≡D m
  sym-≡D : ∀{A}{{_ : Eq A}}{m₁ m₂ : M A} → m₁ ≡D m₂ → m₂ ≡D m₁
  trans-≡D : ∀{A}{{_ : Eq A}}{m₁ m₂ m₃ : M A} → m₁ ≡D m₂ → m₂ ≡D m₃ → m₁ ≡D m₃
  uniform-comm : ∀{A B}{{_ : Eq B}} n → (m : M A) → (f : BitVec n → A → M B)
               → (uniform n >>= λ v → m >>= λ a → f v a) ≡D (m >>= λ a → uniform n >>= λ v → f v a)
  uniform-eq : ∀{A}{{_ : Eq A}} n (f g : BitVec n → M A)
             → (∀ v → f v ≡D g v)
             → (uniform n >>= f) ≡D (uniform n >>= g)
  instance
    EnumerationBitVec        : ∀{n} → Enumeration (BitVec n) 
    EnumerationUnit          : Enumeration ⊤
    EnumerationAdvState      : Enumeration AdvState
    EnumerationOracleState   : Enumeration OracleInit
    EnumerationOracleArg     : Enumeration OracleArg
    EnumerationOracleResult  : Enumeration OracleResult
  any : List Bool → Bool

usesState-CEA : ∀{A} → CryptoExprAlg A Bool
ReturnF       usesState-CEA a = false
UniformF      usesState-CEA n cont = any (map cont (Enumerate it))
GetAdvStateF  usesState-CEA cont = true
SetAdvStateF  usesState-CEA st ce = true
InitOracleF   usesState-CEA st ce = true
CallOracleF   usesState-CEA arg cont = true

usesState-CE : ∀{A} → CryptoExpr A → Bool
usesState-CE = fold-CE usesState-CEA

module _ (OI : OracleImpl) where
  interchange-CE : ∀{A B C}{{_ : Eq C}}(ca : CryptoExpr A)(cb : CryptoExpr B)(f : A → B → CryptoExpr C)
                 → IsFalse (usesState-CE ca) → IsFalse (usesState-CE cb)
                 → eval-CE OI (ca >>= λ a → cb >>= λ b → f a b) ≡D eval-CE OI (cb >>= λ b → ca >>= λ a → f a b)
  interchange-CE (Return a) cb f pfa pfb = refl-≡D _
  interchange-CE (Uniform n cont) cb f pfa pfb =
    trans-≡D (uniform-eq n (λ v → eval-CE OI (cont v >>= λ a → cb >>= λ b → f a b))
                           (λ v → eval-CE OI cb >>= λ b → eval-CE OI (cont v) >>= λ a → eval-CE OI (f a b))
                           λ v → trans-≡D (interchange-CE (cont v) cb f {!!} {!!}) {!!}) $
    trans-≡D (uniform-comm n (eval-CE OI cb) λ v b → eval-CE OI (cont v) >>= λ a → eval-CE OI (f a b)) $
             {!!}
  interchange-CE (GetAdvState cont) cb f () pfb
  interchange-CE (SetAdvState st ca) cb f () pfb
  interchange-CE (InitOracle st ca) cb f () pfb
  interchange-CE (CallOracle arg cont) cb f () pfb

module _ {Q}{{PQ : Probability Q}} where
  open Probability PQ
  postulate
    M-diff : ∀{A}{{_ : Enumeration A}} → M A → M A → Q

  total-diff : ∀{A B}{{_ : Enumeration A}}{{_ : Enumeration B}}
             → (A → M B) → (A → M B)
             → Q
  total-diff f g = sum $ map (λ a → M-diff (f a) (g a)) (Enumerate it)

  postulate
    >>=-l-bound : ∀{A B}{{_ : Enumeration A}}{{_ : Enumeration B}}
                → (x y : M A)(f : A → M B)(q : Q)
                → M-diff x y ≤ q
                → M-diff (x >>= f) (y >>= f) ≤ q
    -- I think this is too strong, we need to look at the 
    >>=-r-bound : ∀{A B}{{_ : Enumeration A}}{{_ : Enumeration B}}
                → (x : M A)(f g : A → M B)(q : Q)
                → M-diff (x >>= f) (x >>= g) ≤ q
                → total-diff f g ≤ q

  module _ (OI₁ OI₂ : OracleImpl) where
    open CryptoExpr
    open BoundOracleUse
    open OracleImpl
    change-oracle-CE : ∀{A b k}{{_ : Enumeration A}}(ce : CryptoExpr A)(q : Q)
                     → total-diff (InitImpl OI₁) (InitImpl OI₂) ≤ q
                     → total-diff (CallImpl OI₁) (CallImpl OI₂) ≤ q
                     → BoundOracleUse b k ce
                     → M-diff (eval-CE OI₁ ce) (eval-CE OI₂ ce) ≤ embed k * q + {!!} -- a little for init
    change-oracle-CE (Return a) q pfi pfc bou = {!!}
    change-oracle-CE (Uniform n cont) q pfi pfc bou = {!!}
    change-oracle-CE (GetAdvState cont) q pfi pfc bou = {!!}
    change-oracle-CE (SetAdvState st ce) q pfi pfc bou = {!!}
    change-oracle-CE (InitOracle st ce) q pfi pfc bou = {!!}
    change-oracle-CE (CallOracle arg cont) q pfi pfc bou = {!!}



