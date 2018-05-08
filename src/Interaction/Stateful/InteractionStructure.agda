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
    StateF    : State IS₁ → State IS₂
    CommandF  : ∀{s} → Command IS₁ s → Command IS₂ (StateF s)
    ResponseF : ∀{s} → {c : Command IS₁ s} → Response IS₂ (CommandF c) → Response IS₁ c
    nextF     : ∀{s} → {c : Command IS₁ s}(r : Response IS₂ (CommandF c)) → StateF (next IS₁ (ResponseF r)) ≡ (next IS₂ r) 
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS r = refl

module _ {IS₁ IS₂ IS₃} where
  comp-IS : ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
  StateF    (comp-IS m₁ m₂) = StateF m₂ ∘′ StateF m₁
  CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
  ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
  nextF     (comp-IS m₁ m₂) r rewrite nextF m₁ (ResponseF m₂ r) | nextF m₂ r  = refl 

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
  _∘′-IS_ = flip comp-IS

module _ {A : Set}{{_ : Eq A}}(ISf : A → InteractionStructure) where
  Tensor-IS : InteractionStructure
  State    Tensor-IS = ∀ a → State (ISf a)
  Command  Tensor-IS sf = Σ A (λ a → Command (ISf a) (sf a))
  Response Tensor-IS {sf} (a , c) = Response (ISf a) c
  next     Tensor-IS {sf} {a , c} r a′ with a == a′
  ... | yes refl = next (ISf a) r
  ... | no   neq = sf a′

module _ {A : Set}{{_ : Eq A}}{ISf : A → InteractionStructure} where
  Inj-IS : ∀{a₀} → (∀{a} → ¬ (a₀ ≡ a) → State (ISf a)) → ISMorphism (ISf a₀) (Tensor-IS ISf)
  StateF    (Inj-IS {a₀} f) sa₀ a with a₀ == a
  ... | yes refl = sa₀
  ... | no   neq = f neq
  CommandF  (Inj-IS {a₀} f) c = a₀ , lem
    where lem : Command (ISf a₀) (StateF (Inj-IS f) _ a₀)
          lem rewrite yes-refl′ a₀ = c
  ResponseF (Inj-IS {a₀} f) r rewrite yes-refl′ a₀ = r
  nextF     (Inj-IS {a₀} f) {s} {c} r = dep-fun-ext _ _ {!!}
    -- I need to force reduction in the argument to StateF, but how?
    where lem : (a : A) → StateF (Inj-IS f) {!!} a ≡ next (Tensor-IS ISf) {StateF (Inj-IS f) s} {a₀ , {!!}} {!!} a
          lem = {!!}

{-
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
  bimap-IS m₁ m₂ = tensormap-IS λ { false → m₁ ; true → m₂ }

-}
