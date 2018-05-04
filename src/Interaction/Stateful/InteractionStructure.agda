{-# OPTIONS --allow-unsolved-metas #-}
module Interaction.Stateful.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.FunExt
open import Algebra.BinaryRelation

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}{c : Command s}(r : Response c) → State
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set₁ where
  field
    StateF    : BinaryRelation (State IS₁) (State IS₂)
  open BinaryRelation StateF
  field
    CommandF  : ∀{s s′} → (pf : Relation-BR s s′) → Command IS₁ s → Command IS₂ s′
    ResponseF : ∀{s s′} → (pf : Relation-BR s s′) → {c : Command IS₁ s} → Response IS₂ (CommandF pf c) → Response IS₁ c
    nextF     : ∀{s s′} → (pf : Relation-BR s s′) → {c : Command IS₁ s}(r : Response IS₂ (CommandF pf c))
              → Relation-BR (next IS₁ (ResponseF pf r)) (next IS₂ r) 
open ISMorphism

{-
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
  bincase : ∀{l}{A : Set l}(a₁ a₂ : A) → Bool → A
  bincase a₁ a₂ false = a₁
  bincase a₁ a₂ true  = a₂

module _ IS₁ IS₂ where
  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure
  _⊕-IS_ = Tensor-IS (bincase IS₁ IS₂)

module _ {IS₁ IS₂}  where
  InjL-IS : ISMorphism IS₁ (IS₁ ⊕-IS IS₂)
  InjL-IS = Inj-IS {ISf = bincase IS₁ IS₂} {false}
  InjR-IS : ISMorphism IS₂ (IS₁ ⊕-IS IS₂)
  InjR-IS = Inj-IS {ISf = bincase IS₁ IS₂} {true}

module _ {IS₁ IS₂ JS₁ JS₂} where
  bimap-IS : ISMorphism IS₁ JS₁ → ISMorphism IS₂ JS₂ → ISMorphism (IS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂)
  StateF    (bimap-IS m₁ m₂)  s   false = StateF m₁ (s false)
  StateF    (bimap-IS m₁ m₂)  s   true  = StateF m₂ (s true)
  CommandF  (bimap-IS m₁ m₂) {s} (false , c) = false , CommandF m₁ c
  CommandF  (bimap-IS m₁ m₂) {s} (true  , c) = true  , CommandF m₂ c
  ResponseF (bimap-IS m₁ m₂) {s} {false , c} r = ResponseF m₁ r
  ResponseF (bimap-IS m₁ m₂) {s} {true  , c} r = ResponseF m₂ r
  nextF     (bimap-IS m₁ m₂) {s} {false , c} r = dep-fun-ext _ _ λ { false → nextF m₁ r ; true → refl       }
  nextF     (bimap-IS m₁ m₂) {s} {true  , c} r = dep-fun-ext _ _ λ { false → refl       ; true → nextF m₂ r }

-}
