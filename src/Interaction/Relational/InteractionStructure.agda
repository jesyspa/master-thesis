module Interaction.Relational.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.Relation
open import Algebra.FunExt

record InteractionStructure (State : Set) : Set₁ where
  field
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}{c : Command s}(r : Response c) → State
open InteractionStructure

IStruct = InteractionStructure

record ISMorphism {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(SR : Relation S₁ S₂) : Set₁ where
  field
    CommandF  : ∀{s s′} → SR s s′ → Command IS₁ s → Command IS₂ s′
    ResponseF : ∀{s s′}(sr : SR s s′){c : Command IS₁ s} → Response IS₂ (CommandF sr c) → Response IS₁ c
    nextF     : ∀{s s′}(sr : SR s s′){c : Command IS₁ s}(r : Response IS₂ (CommandF sr c)) → SR (next IS₁ (ResponseF sr r)) (next IS₂ r) 
open ISMorphism

id-IS : ∀{S}{IS : IStruct S} → ISMorphism IS IS _≡_
CommandF  id-IS refl = id
ResponseF id-IS refl = id
nextF     id-IS refl r = refl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{sf sg} where
  comp-IS : ISMorphism IS₁ IS₂ sf → ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₃ (comp-R sf sg)
  CommandF  (comp-IS m₁ m₂) (s₂ , p₁ , p₂) = CommandF m₂ p₂ ∘′ CommandF m₁ p₁
  ResponseF (comp-IS m₁ m₂) (s₂ , p₁ , p₂) = ResponseF m₁ p₁ ∘′ ResponseF m₂ p₂
  nextF     (comp-IS m₁ m₂) (s₂ , p₁ , p₂) r = next IS₂ (ResponseF m₂ p₂ r) , nextF m₁ p₁ (ResponseF m₂ p₂ r) , nextF m₂ p₂ r

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₂ sf → ISMorphism IS₁ IS₃ (comp-R sf sg)
  _∘′-IS_ = flip comp-IS

TensorUnit-IS : InteractionStructure ⊤
Command  TensorUnit-IS  tt = ⊥
Response TensorUnit-IS {tt} ()
next     TensorUnit-IS {tt} {()}

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂) where
  BinTensor-IS : InteractionStructure (S₁ × S₂)
  Command      BinTensor-IS (s₁ , s₂) = Command IS₁ s₁ ⊎ Command IS₂ s₂
  Response     BinTensor-IS {s₁ , s₂} (left  c) = Response IS₁ c
  Response     BinTensor-IS {s₁ , s₂} (right c) = Response IS₂ c
  next         BinTensor-IS {s₁ , s₂} {left  c} r = next IS₁ r , s₂
  next         BinTensor-IS {s₁ , s₂} {right c} r = s₁ , next IS₂ r

  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure (S₁ × S₂)
  _⊕-IS_ = BinTensor-IS

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂} where
  IncL-IS : ISMorphism IS₁ (BinTensor-IS IS₁ IS₂) incL-R
  CommandF   IncL-IS {.s₁} {s₁ , s₂} refl c = left c
  ResponseF  IncL-IS {.s₁} {s₁ , s₂} refl r = r
  nextF      IncL-IS {.s₁} {s₁ , s₂} refl r = refl

  IncR-IS : ISMorphism IS₂ (BinTensor-IS IS₁ IS₂) incR-R
  CommandF   IncR-IS {.s₂} {s₁ , s₂} refl c = right c
  ResponseF  IncR-IS {.s₂} {s₁ , s₂} refl r = r
  nextF      IncR-IS {.s₂} {s₁ , s₂} refl r = refl

module _ {S₁ S₂ T₁ T₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{JS₁ : IStruct T₁}{JS₂ : IStruct T₂}{R₁ R₂} where
  binmap-IS : ISMorphism IS₁ JS₁ R₁ → ISMorphism IS₂ JS₂ R₂ → ISMorphism (IS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂) (parcomp-R R₁ R₂)
  CommandF  (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) (left  c)   = left  $ CommandF m₁ p₁ c
  CommandF  (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) (right c)   = right $ CommandF m₂ p₂ c
  ResponseF (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) {left  c} r = ResponseF m₁ p₁ r
  ResponseF (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) {right c} r = ResponseF m₂ p₂ r
  nextF     (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) {left  c} r = nextF m₁ p₁ r , p₂
  nextF     (binmap-IS m₁ m₂) {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) {right c} r = p₁ , nextF m₂ p₂ r

{-
postulate
  LeftCancel-IS    : ∀{S}{IS : IStruct S} → ISMorphism (BinTensor-IS TensorUnit-IS IS) IS snd 
  RightCancel-IS   : ∀{S}{IS : IStruct S} → ISMorphism (BinTensor-IS IS TensorUnit-IS) IS fst
  LeftUncancel-IS  : ∀{S}{IS : IStruct S} → ISMorphism IS (BinTensor-IS TensorUnit-IS IS) (λ s → tt , s)
  RightUncancel-IS : ∀{S}{IS : IStruct S} → ISMorphism IS (BinTensor-IS IS TensorUnit-IS) (λ s → s , tt)

-}
