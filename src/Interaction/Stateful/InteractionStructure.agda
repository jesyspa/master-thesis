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

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set₁ where
  field
    StateF    : State IS₁ → State IS₂ → Set
    CommandF  : ∀{s s′} → (pf : StateF s s′) → Command IS₁ s → Command IS₂ s′
    ResponseF : ∀{s s′} → (pf : StateF s s′) → {c : Command IS₁ s} → Response IS₂ (CommandF pf c) → Response IS₁ c
    nextF     : ∀{s s′} → (pf : StateF s s′) → {c : Command IS₁ s}(r : Response IS₂ (CommandF pf c))
              → StateF (next IS₁ (ResponseF pf r)) (next IS₂ r) 
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = _≡_
CommandF  id-IS refl = id
ResponseF id-IS refl = id
nextF     id-IS refl r = refl

module _ {IS₁ IS₂ IS₃} where
  comp-IS : ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
  StateF    (comp-IS m₁ m₂) s₁ s₃ = Σ (State IS₂) λ s₂ → StateF m₁ s₁ s₂ × StateF m₂ s₂ s₃
  CommandF  (comp-IS m₁ m₂) (s₂ , p₁ , p₂) = CommandF m₂ p₂ ∘′ CommandF m₁ p₁
  ResponseF (comp-IS m₁ m₂) (s₂ , p₁ , p₂) = ResponseF m₁ p₁ ∘′ ResponseF m₂ p₂
  nextF     (comp-IS m₁ m₂) (s₂ , p₁ , p₂) r = next IS₂ (ResponseF m₂ p₂ r) , nextF m₁ p₁ (ResponseF m₂ p₂ r) , nextF m₂ p₂ r

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
  _∘′-IS_ = flip comp-IS

Zero-IS : InteractionStructure
State    Zero-IS = ⊤
Command  Zero-IS tt = ⊥
Response Zero-IS ()
next     Zero-IS {tt} {()}

⊥-IS = Zero-IS

init-IS : ∀{IS} → ISMorphism Zero-IS IS
StateF    init-IS tt s = ⊥
CommandF  init-IS ()
ResponseF init-IS ()
nextF     init-IS ()

-- Unit is probably definable, but we don't need it right now.

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
  StateF    (Inj-IS {a}) sa sf = sa ≡ sf a
  CommandF  (Inj-IS {a}) refl c = a , c
  ResponseF (Inj-IS {a}) refl r = r
  nextF     (Inj-IS {a}) refl r with a == a
  ... | yes refl = refl
  ... | no   neq = ⊥-elim (neq refl)

module _ {A : Set}{{_ : Eq A}}{ISf ISg : A → InteractionStructure} where
  tensormap-IS : (∀ a → ISMorphism (ISf a) (ISg a)) → ISMorphism (Tensor-IS ISf) (Tensor-IS ISg)
  StateF    (tensormap-IS mf) sf sg        = ∀ a → StateF (mf a) (sf a) (sg a)
  CommandF  (tensormap-IS mf) pf (a , c)   = a , CommandF (mf a) (pf a) c
  ResponseF (tensormap-IS mf) pf {a , c} r = ResponseF (mf a) (pf a) r
  nextF     (tensormap-IS mf) pf {a , c} r a′ with a == a′
  ... | yes refl = nextF (mf a) (pf a) r
  ... | no   neq = pf a′

private
  bincase : ∀{l}{A : Set l}(a₁ a₂ : A) → Bool → A
  bincase a₁ a₂ false = a₁
  bincase a₁ a₂ true  = a₂

  dep-bincase : ∀{l}{A₁ A₂ : Set l}(a₁ : A₁)(a₂ : A₂) → (b : Bool) → bincase A₁ A₂ b
  dep-bincase a₁ a₂ false = a₁
  dep-bincase a₁ a₂ true  = a₂

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
  bimap-IS m₁ m₂ = tensormap-IS λ { false → m₁ ; true → {!m₂!} }
