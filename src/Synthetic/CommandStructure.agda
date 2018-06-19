{-# OPTIONS --type-in-type #-}
module Synthetic.CommandStructure where

open import ThesisPrelude

record CommandStructure : Set₁ where
  field
    Command  : Set
    Response : Command → Set
CmdStruct = CommandStructure

record CmdMorphism (C₁ C₂ : CmdStruct) : Set where
  open CommandStructure
  field
    CommandF : Command C₁ → Command C₂
    ResponseF : ∀{c} → Response C₂ (CommandF c) → Response C₁ c

record CmdMorphismSim {C₁ C₂}(m₁ m₂ : CmdMorphism C₁ C₂) : Set where
  open CommandStructure
  open CmdMorphism
  field
    CommandEq  : ∀ c → CommandF m₁ c ≡ CommandF m₂ c
    ResponseEq : ∀{c}(r : Response C₂ (CommandF m₁ c))
               → ResponseF m₁ r ≡ ResponseF m₂ (transport (Response C₂) (CommandEq c) r) 

infix 4 _≡C_
_≡C_ = CmdMorphismSim

module FMBegin C where
  open CommandStructure C
  data FreeMonad : Set → Set where
    Return-FM : ∀{A} → A → FreeMonad A
    Invoke-FM : ∀{A} → (c : Command) → (Response c → FreeMonad A) → FreeMonad A
  
  CommandAlgebra : Set → Set
  CommandAlgebra R = (c : Command) → (Response c → R) → R
  
  fold-algebra : ∀{A R} → CommandAlgebra R → (A → R) → FreeMonad A → R
  fold-algebra alg f (Return-FM a) = f a
  fold-algebra alg f (Invoke-FM c cont) = alg c (λ r → fold-algebra alg f (cont r))

  id-Alg : ∀{R} → CommandAlgebra (FreeMonad R)
  id-Alg = Invoke-FM

module _ {C} where
  open CommandStructure C
  open FMBegin C
  fmap-FM : ∀{A B} → (A → B) → FreeMonad A → FreeMonad B
  fmap-FM f = fold-algebra id-Alg (Return-FM ∘′ f)

  instance
    FunctorFM : Functor FreeMonad
    fmap {{FunctorFM}} = fmap-FM

  ap-FM : ∀{A B} → FreeMonad (A → B) → FreeMonad A → FreeMonad B
  ap-FM mf ma = fold-algebra id-Alg (flip fmap ma) mf

  bind-FM : ∀{A B} → FreeMonad A → (A → FreeMonad B) → FreeMonad B
  bind-FM m f = fold-algebra id-Alg f m

  instance
    ApplicativeFM : Applicative FreeMonad
    pure {{ApplicativeFM}} = Return-FM
    _<*>_ {{ApplicativeFM}} = ap-FM
    MonadFM : Monad FreeMonad
    _>>=_ {{MonadFM}} = bind-FM

  smart-constructor : (c : Command) → FreeMonad (Response c)
  smart-constructor c = Invoke-FM c Return-FM


module FM C where
  open FMBegin C public 
  open CommandStructure C
  MonadicCommandAlgebra : (Set → Set) → Set
  MonadicCommandAlgebra M = (c : Command) → M (Response c) 

  id-MAlg : MonadicCommandAlgebra FreeMonad
  id-MAlg = smart-constructor

  demonadise-algebra : ∀{A M}{{_ : Monad M}} → MonadicCommandAlgebra M → CommandAlgebra (M A)
  demonadise-algebra alg c cont = alg c >>= cont

  fold-monadic-algebra : ∀{M A}{{_ : Monad M}} → MonadicCommandAlgebra M → FreeMonad A → M A
  fold-monadic-algebra alg = fold-algebra (demonadise-algebra alg) return

module _ {C₁ C₂} where
  open CmdMorphism
  open FM
  fmap-CS-MAlg : CmdMorphism C₁ C₂ → MonadicCommandAlgebra C₁ (FreeMonad C₂)
  fmap-CS-MAlg m c = Invoke-FM (CommandF m c) λ r → Return-FM (ResponseF m r)

  fmap-CS-FM : ∀{A} → CmdMorphism C₁ C₂ → FreeMonad C₁ A → FreeMonad C₂ A
  fmap-CS-FM m = fold-monadic-algebra C₁ (fmap-CS-MAlg m)

module _ (F : Set → Set) where
  open CommandStructure
  Forget : CmdStruct
  Command  Forget = Σ Set λ A → F A
  Response Forget (A , m) = A

open FM

CmdMonad : CmdStruct → CmdStruct
CmdMonad = Forget ∘ FreeMonad

Interpretation : CmdStruct → CmdStruct → Set
Interpretation C₁ C₂ = CmdMorphism C₁ (CmdMonad C₂)

module _ {C M}{{_ : Monad M}}(cm : CmdMorphism C (Forget M)) where
  open CmdMorphism cm
  Conjugate : ∀{A} → FreeMonad C A → M A
  Conjugate (Return-FM a) = return a
  Conjugate (Invoke-FM c cont) with CommandF c | graphAt CommandF c
  ... | B , mb | ingraph refl = mb >>= λ r → Conjugate (cont (ResponseF r)) 

module _ {C M}{{_ : Monad M}}(f : ∀{A} → FreeMonad C A → M A) where
  open CommandStructure
  open CmdMorphism
  Conjugate′ : CmdMorphism C (Forget M)
  CommandF  Conjugate′ c = Response C c , f (smart-constructor c)
  ResponseF Conjugate′ r = r

Cong-Interp : ∀{C₁ C₂ A} → Interpretation C₁ C₂ → FreeMonad C₁ A → FreeMonad C₂ A
Cong-Interp interp = Conjugate interp
