module Synthetic.CryptoExpr where

open import ThesisPrelude
open import Utility.Vector.Definition
open import Utility.List.Elem.Definition
open import Probability.Class

record CryptoState : Set₁ where
  field
    AdvState     : Set
    OracleState  : Set
    OracleArg    : Set
    OracleResult : Set

record Enumeration (A : Set) : Set where
  field
    Enumerate : List A
    EnumerateComplete : ∀ a → a ∈ Enumerate
    EnumerateUnique : ∀{a}(p q : a ∈ Enumerate) → p ≡ q
open Enumeration

module _ CS where
  open CryptoState CS
  data CryptoExpr : (S : Set) → Set where
    Return      : ∀{A} → A                                           → CryptoExpr A
    Uniform     : ∀{A} → (n : Nat)   → (BitVec n     → CryptoExpr A) → CryptoExpr A
    GetAdvState : ∀{A}               → (AdvState     → CryptoExpr A) → CryptoExpr A
    SetAdvState : ∀{A} → AdvState    →                 CryptoExpr A  → CryptoExpr A
    InitOracle  : ∀{A} → OracleState →                 CryptoExpr A  → CryptoExpr A
    CallOracle  : ∀{A} → OracleArg   → (OracleResult → CryptoExpr A) → CryptoExpr A

  record CryptoExprAlg (A R : Set) : Set₁ where
    field
      ReturnF       : A → R
      UniformF      : ∀ n → (BitVec n → R) → R
      GetAdvStateF  : (AdvState → R) → R
      SetAdvStateF  : AdvState → R → R
      InitOracleF   : OracleState → R → R
      CallOracleF   : OracleArg → (OracleResult → R) → R

module _ {CS} where
  open CryptoState CS

  module _ {A R}(CEA : CryptoExprAlg CS A R) where
    open CryptoExprAlg CEA
    fold-CE : CryptoExpr CS A → R
    fold-CE (Return a) = ReturnF a
    fold-CE (Uniform n cont) = UniformF n λ v → fold-CE (cont v)
    fold-CE (GetAdvState cont) = GetAdvStateF λ st → fold-CE (cont st)
    fold-CE (SetAdvState st ce) = SetAdvStateF st (fold-CE ce)
    fold-CE (InitOracle st ce) = InitOracleF st (fold-CE ce)
    fold-CE (CallOracle arg cont) = CallOracleF arg λ r → fold-CE (cont r)

  open CryptoExprAlg
  module _ {A B}(f : A → B) where
    fmap-CEA : CryptoExprAlg CS A (CryptoExpr CS B)
    ReturnF      fmap-CEA = Return ∘′ f
    UniformF     fmap-CEA = Uniform
    GetAdvStateF fmap-CEA = GetAdvState
    SetAdvStateF fmap-CEA = SetAdvState
    InitOracleF  fmap-CEA = InitOracle
    CallOracleF  fmap-CEA = CallOracle

    fmap-CE : CryptoExpr CS A → CryptoExpr CS B
    fmap-CE = fold-CE fmap-CEA

  instance
    FunctorCE : Functor (CryptoExpr CS)
    fmap {{FunctorCE}} = fmap-CE

  module _ {A B} where
    ap-CEA : CryptoExprAlg CS (A → B) (CryptoExpr CS A → CryptoExpr CS B)
    ReturnF      ap-CEA f ce        = fmap f ce
    UniformF     ap-CEA n cont ce   = Uniform n λ v → cont v ce
    GetAdvStateF ap-CEA cont ce     = GetAdvState λ st → cont st ce
    SetAdvStateF ap-CEA st cont ce  = SetAdvState st (cont ce)
    InitOracleF  ap-CEA st cont ce  = InitOracle st (cont ce)
    CallOracleF  ap-CEA arg cont ce = CallOracle arg λ r → cont r ce

    ap-CE : CryptoExpr CS (A → B) → CryptoExpr CS A → CryptoExpr CS B
    ap-CE = fold-CE ap-CEA

    bind-CEA : CryptoExprAlg CS A ((A → CryptoExpr CS B) → CryptoExpr CS B)
    ReturnF      bind-CEA a ce        = ce a
    UniformF     bind-CEA n cont ce   = Uniform n λ v → cont v ce
    GetAdvStateF bind-CEA cont ce     = GetAdvState λ st → cont st ce
    SetAdvStateF bind-CEA st cont ce  = SetAdvState st (cont ce)
    InitOracleF  bind-CEA st cont ce  = InitOracle st (cont ce)
    CallOracleF  bind-CEA arg cont ce = CallOracle arg λ r → cont r ce

    bind-CE : CryptoExpr CS A → (A → CryptoExpr CS B) → CryptoExpr CS B
    bind-CE = fold-CE bind-CEA

  instance
    ApplicativeCE : Applicative (CryptoExpr CS)
    pure  {{ApplicativeCE}} = Return
    _<*>_ {{ApplicativeCE}} = ap-CE
    MonadCE : Monad (CryptoExpr CS)
    _>>=_ {{MonadCE}} = bind-CE

  postulate
    M : Set → Set
    instance
      FunctorM     : Functor M
      ApplicativeM : Applicative M
      MonadM       : Monad M
    uniform : (n : Nat) → M (BitVec n)
    setAdvState : AdvState → M ⊤
    getAdvState : M AdvState
  
  record OracleImpl : Set₁ where
    field
      InitImpl : OracleState → M ⊤
      CallImpl : OracleArg → M OracleResult
  
  module _ (OI : OracleImpl) where
    open OracleImpl OI
    eval-CEA : ∀{A} → CryptoExprAlg CS A (M A)
    ReturnF      eval-CEA a     = return a
    UniformF     eval-CEA n m   = uniform n >>= m
    GetAdvStateF eval-CEA m     = getAdvState >>= m
    SetAdvStateF eval-CEA st m  = setAdvState st >> m
    InitOracleF  eval-CEA st m  = InitImpl st >> m
    CallOracleF  eval-CEA arg m = CallImpl arg >>= m
    
    eval-CE : ∀{A} → CryptoExpr CS A → M A
    eval-CE = fold-CE eval-CEA
  
  postulate
    _≡D_ : ∀{A} → M A → M A → Set
    instance
      EnumerationBitVec        : ∀{n} → Enumeration (BitVec n) 
      EnumerationAdvState      : Enumeration AdvState
      EnumerationOracleState   : Enumeration OracleState
      EnumerationOracleArg     : Enumeration OracleArg
      EnumerationOracleResult  : Enumeration OracleResult
    -- We need a proof the list is non-empty, but eh.
    -- For probabilities, we can always take 0.
    maximum : ∀{A : Set}{{_ : Ord A}} → List A → A
    any : List Bool → Bool

  oracleUses-CEA : ∀{A} → CryptoExprAlg CS A Nat
  ReturnF       oracleUses-CEA a = zero
  UniformF      oracleUses-CEA n cont = maximum (map cont (Enumerate it))
  GetAdvStateF  oracleUses-CEA cont = maximum (map cont (Enumerate it)) 
  SetAdvStateF  oracleUses-CEA st ce = ce
  InitOracleF   oracleUses-CEA st ce = ce
  CallOracleF   oracleUses-CEA arg cont = maximum (map cont (Enumerate it)) 

  oracleUses-CE : ∀{A} → CryptoExpr CS A → Nat
  oracleUses-CE = fold-CE oracleUses-CEA

  usesState-CEA : ∀{A} → CryptoExprAlg CS A Bool
  ReturnF       usesState-CEA a = false
  UniformF      usesState-CEA n cont = any (map cont (Enumerate it))
  GetAdvStateF  usesState-CEA cont = true
  SetAdvStateF  usesState-CEA st ce = true
  InitOracleF   usesState-CEA st ce = true
  CallOracleF   usesState-CEA arg cont = any (map cont (Enumerate it))

  usesState-CE : ∀{A} → CryptoExpr CS A → Bool
  usesState-CE = fold-CE usesState-CEA

  module _ (OI : OracleImpl) where
    interchange-CE : ∀{A B C}(ca : CryptoExpr CS A)(cb : CryptoExpr CS B)(f : A → B → CryptoExpr CS C)
                   → IsFalse (usesState-CE ca) → IsFalse (usesState-CE cb)
                   → eval-CE OI (ca >>= λ a → cb >>= λ b → f a b) ≡D eval-CE OI (cb >>= λ b → ca >>= λ a → f a b)
    interchange-CE ca cb f = {!!}
