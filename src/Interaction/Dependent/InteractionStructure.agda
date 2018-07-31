module Interaction.Dependent.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.FunExt

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}(c : Command s) → State
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set₁ where
  field
    StateF    : State IS₁ → State IS₂
    CommandF  : ∀{s} → Command IS₁ s → Command IS₂ (StateF s)
    ResponseF : ∀{s} → {c : Command IS₁ s} → Response IS₂ (CommandF c) → Response IS₁ c
    nextF     : ∀{s} → (c : Command IS₁ s) → StateF (next IS₁ c) ≡ (next IS₂ (CommandF c)) 
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS c = refl

module _ {IS₁ IS₂ IS₃} where
  comp-IS : ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
  StateF    (comp-IS m₁ m₂) = StateF m₂ ∘′ StateF m₁
  CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
  ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
  nextF     (comp-IS m₁ m₂) c rewrite nextF m₁ c | nextF m₂ (CommandF m₁ c) = refl

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
  _∘′-IS_ = flip comp-IS

TensorUnit-IS : InteractionStructure
State    TensorUnit-IS = ⊤
Command  TensorUnit-IS  tt = ⊥
Response TensorUnit-IS {tt} ()
next     TensorUnit-IS {tt} ()

module _ {A : Set}{{_ : Eq A}}(ISf : A → InteractionStructure) where
  -- While nice theoretically, implementing morphisms for this structure is a pain.
  Tensor-IS : InteractionStructure
  State    Tensor-IS              = ∀ a → State (ISf a)
  Command  Tensor-IS  sf          = Σ A λ a → Command (ISf a) (sf a)
  Response Tensor-IS {sf} (a , c) = Response (ISf a) c
  next     Tensor-IS {sf} (a , c) a′ with a == a′
  ... | yes refl = next (ISf a) c
  ... | no   neq = sf a′

module _ IS₁ IS₂ where
  BinTensor-IS : InteractionStructure
  State        BinTensor-IS = State IS₁ × State IS₂
  Command      BinTensor-IS (s₁ , s₂) = Command IS₁ s₁ ⊎ Command IS₂ s₂
  Response     BinTensor-IS {s₁ , s₂} (left  c) = Response IS₁ c
  Response     BinTensor-IS {s₁ , s₂} (right c) = Response IS₂ c
  next         BinTensor-IS {s₁ , s₂} (left  c) = next IS₁ c , s₂
  next         BinTensor-IS {s₁ , s₂} (right c) = s₁ , next IS₂ c

  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure
  _⊕-IS_ = BinTensor-IS

module _ {IS₁ IS₂} where
  IncL-IS : State IS₂ → ISMorphism IS₁ (BinTensor-IS IS₁ IS₂)
  StateF     (IncL-IS s₂) s₁ = s₁ , s₂
  CommandF   (IncL-IS s₂) c = left c
  ResponseF  (IncL-IS s₂) r = r
  nextF      (IncL-IS s₂) c = refl

  IncR-IS : State IS₁ → ISMorphism IS₂ (BinTensor-IS IS₁ IS₂)
  StateF     (IncR-IS s₁) s₂ = s₁ , s₂
  CommandF   (IncR-IS s₁) c = right c
  ResponseF  (IncR-IS s₁) r = r
  nextF      (IncR-IS s₁) c = refl

module _ {IS₁ IS₂ JS₁ JS₂} where
  binmap-IS : ISMorphism IS₁ JS₁ → ISMorphism IS₂ JS₂ → ISMorphism (IS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂)
  StateF    (binmap-IS m₁ m₂) (s₁ , s₂) = StateF m₁ s₁ , StateF m₂ s₂
  CommandF  (binmap-IS m₁ m₂) {s₁ , s₂} (left  c) = left  $ CommandF m₁ c
  CommandF  (binmap-IS m₁ m₂) {s₁ , s₂} (right c) = right $ CommandF m₂ c
  ResponseF (binmap-IS m₁ m₂) {s₁ , s₂} {left  c} r = ResponseF m₁ r
  ResponseF (binmap-IS m₁ m₂) {s₁ , s₂} {right c} r = ResponseF m₂ r
  nextF     (binmap-IS m₁ m₂) {s₁ , s₂} (left  c) rewrite nextF m₁ c = refl
  nextF     (binmap-IS m₁ m₂) {s₁ , s₂} (right c) rewrite nextF m₂ c = refl

postulate
  LeftCancel-IS    : ∀{IS} → ISMorphism (TensorUnit-IS ⊕-IS IS) IS
  RightCancel-IS   : ∀{IS} → ISMorphism (IS ⊕-IS TensorUnit-IS) IS
  LeftUncancel-IS  : ∀{IS} → ISMorphism IS (TensorUnit-IS ⊕-IS IS)
  RightUncancel-IS : ∀{IS} → ISMorphism IS (IS ⊕-IS TensorUnit-IS)

BinTensor*-IS : List InteractionStructure → InteractionStructure
BinTensor*-IS = foldr BinTensor-IS TensorUnit-IS
