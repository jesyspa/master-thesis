{-# OPTIONS --type-in-type #-}
module Synthetic.CommandStructure where

open import ThesisPrelude

record CommandStructure : Set₁ where
  field
    Command  : Set
    Response : Command → Set

record CmdMorphism (C₁ C₂ : CommandStructure) : Set where
  open CommandStructure
  field
    CommandF : Command C₁ → Command C₂
    ResponseF : ∀{c} → Response C₂ (CommandF c) → Response C₁ c

module FM C where
  open CommandStructure C
  data FreeMonad : Set → Set where
    Return-FM : ∀{A} → A → FreeMonad A
    Invoke-FM : ∀{A} → (c : Command) → (Response c → FreeMonad A) → FreeMonad A
  
  CommandAlgebra : Set → Set₁
  CommandAlgebra R = (c : Command) → (Response c → R) → R
  
  FoldAlgebra : ∀{A R} → CommandAlgebra R → (A → R) → FreeMonad A → R
  FoldAlgebra alg f (Return-FM a) = f a
  FoldAlgebra alg f (Invoke-FM c cont) = alg c (λ r → FoldAlgebra alg f (cont r))

  id-Alg : ∀{R} → CommandAlgebra (FreeMonad R)
  id-Alg c cont = Invoke-FM c cont
  
module _ {C} where
  open CommandStructure C
  open FM C
  fmap-FM : ∀{A B} → (A → B) → FreeMonad A → FreeMonad B
  fmap-FM f = FoldAlgebra id-Alg (Return-FM ∘′ f)

  instance
    FunctorFM : Functor FreeMonad
    fmap {{FunctorFM}} = fmap-FM

  ap-FM : ∀{A B} → FreeMonad (A → B) → FreeMonad A → FreeMonad B
  ap-FM mf ma = FoldAlgebra id-Alg (flip fmap ma) mf

  bind-FM : ∀{A B} → FreeMonad A → (A → FreeMonad B) → FreeMonad B
  bind-FM m f = FoldAlgebra id-Alg f m

  instance
    ApplicativeFM : Applicative FreeMonad
    pure {{ApplicativeFM}} = Return-FM
    _<*>_ {{ApplicativeFM}} = ap-FM
    MonadFM : Monad FreeMonad
    _>>=_ {{MonadFM}} = bind-FM

module _ (F : Set → Set) where
  open CommandStructure
  Forget : CommandStructure
  Command  Forget = Σ Set λ A → F A
  Response Forget (A , m) = A

open FM

CmdMonad : CommandStructure → CommandStructure
CmdMonad = Forget ∘ FreeMonad

Interpretation : CommandStructure → CommandStructure → Set
Interpretation C₁ C₂ = CmdMorphism C₁ (CmdMonad C₂)

module _ {C M}{{_ : Monad M}}(cm : CmdMorphism C (Forget M)) where
  open CmdMorphism cm
  Conjugate : ∀{A} → FreeMonad C A → M A
  Conjugate (Return-FM a) = return a
  Conjugate (Invoke-FM c cont) with CommandF c | graphAt CommandF c
  ... | B , mb | ingraph refl = mb >>= λ r → Conjugate (cont (ResponseF r)) 

Cong-Interp : ∀{C₁ C₂ A} → Interpretation C₁ C₂ → FreeMonad C₁ A → FreeMonad C₂ A
Cong-Interp interp = Conjugate interp
