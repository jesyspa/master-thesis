{-# OPTIONS --allow-unsolved-metas #-}
module Interaction.Stateful.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.FunExt

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}{c : Command s}(r : Response c) → State
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    StateF    : State IS₂ → State IS₁
    CommandF  : ∀{s} → Command IS₁ (StateF s) → Command IS₂ s
    ResponseF : ∀{s}{c : Command IS₁ (StateF s)} → Response IS₂ (CommandF c) → Response IS₁ c
    nextF     : ∀{s}{c : Command IS₁ (StateF s)}(r : Response IS₂ (CommandF c))
              → StateF (next IS₂ r) ≡ next IS₁ (ResponseF r)
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS r = refl

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
StateF    (comp-IS m₁ m₂) = StateF m₁ ∘′ StateF m₂
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
nextF     (comp-IS m₁ m₂) r rewrite nextF m₂ r | nextF m₁ (ResponseF m₂ r) = refl

infixr 9 _∘′-IS_
_∘′-IS_ : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
_∘′-IS_ = flip comp-IS

Zero-IS : InteractionStructure
State    Zero-IS = ⊤
Command  Zero-IS tt = ⊥
Response Zero-IS ()
next     Zero-IS {tt} {()}

⊥-IS = Zero-IS

init-IS : ∀{IS} → ISMorphism Zero-IS IS
StateF    init-IS _ = tt
CommandF  init-IS ()
ResponseF init-IS {_} {()}
nextF     init-IS {_} {()} _

Unit-IS : InteractionStructure
State    Unit-IS = ⊥
Command  Unit-IS ()
Response Unit-IS {()}
next     Unit-IS {()}

⊤-IS = Unit-IS

term-IS : ∀{IS} → ISMorphism IS Unit-IS
StateF    term-IS ()
CommandF  term-IS {()}
ResponseF term-IS {()}
nextF     term-IS {()}

module _ {A : Set}{{_ : Eq A}}(ISf : A → InteractionStructure) where
  Tensor-IS : InteractionStructure
  State    Tensor-IS = ∀ a → State (ISf a)
  Command  Tensor-IS sf = Σ A (λ a → Command (ISf a) (sf a))
  Response Tensor-IS {sf} (a , c) = Response (ISf a) c
  next     Tensor-IS {sf} {a , c} r a′ with a == a′
  ... | yes refl = next (ISf a) r
  ... | no   neq = sf a′

module _ {A : Set}{{_ : Eq A}}{ISf : A → InteractionStructure} where
  Inj-IS : ∀{a} → ISMorphism (ISf a) (Tensor-IS ISf)
  StateF    (Inj-IS {a}) sf = sf a
  CommandF  (Inj-IS {a}) c  = a , c
  ResponseF (Inj-IS {a}) r  = r
  nextF     (Inj-IS {a}) r with a == a
  ... | yes refl = refl
  ... | no   neq = ⊥-elim (neq refl)

private
  bincase : (IS₁ IS₂ : InteractionStructure) → Bool → InteractionStructure
  bincase IS₁ IS₂ false = IS₁
  bincase IS₁ IS₂ true  = IS₂

module _ (IS₁ IS₂ : InteractionStructure) where
  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure
  _⊕-IS_ = Tensor-IS (bincase IS₁ IS₂)

module _ {IS₁ IS₂ : InteractionStructure} where
  InjL-IS : ISMorphism IS₁ (IS₁ ⊕-IS IS₂)
  InjL-IS = Inj-IS {ISf = bincase IS₁ IS₂} {false}
  InjR-IS : ISMorphism IS₂ (IS₁ ⊕-IS IS₂)
  InjR-IS = Inj-IS {ISf = bincase IS₁ IS₂} {true}
