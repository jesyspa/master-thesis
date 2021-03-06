module Interaction.Indexed.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Utility.BTAll
open import Algebra.Function

record InteractionStructure (S : BTree Set) : Set₁ where
  field
    Command     : BTAll′ S → Set
    Response    : {s : BTAll′ S} → Command s → Set
    next        : {s : BTAll′ S}(c : Command s)(r : Response c) → BTAll′ S
open InteractionStructure

IStruct = InteractionStructure

record ISMorphism {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(StateF : BTAll′ S₁ → BTAll′ S₂) : Set₁ where
  field
    CommandF  : ∀{s} → Command IS₁ s → Command IS₂ (StateF s)
    ResponseF : ∀{s} → {c : Command IS₁ s} → Response IS₂ (CommandF c) → Response IS₁ c
    nextF     : ∀{s} → {c : Command IS₁ s}(r : Response IS₂ (CommandF c)) → StateF (next IS₁ c (ResponseF r)) ≡ (next IS₂ (CommandF c) r) 
open ISMorphism

id-IS : ∀{S}{IS : IStruct S} → ISMorphism IS IS id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS r = refl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{sf sg} where
  comp-IS : ISMorphism IS₁ IS₂ sf → ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
  ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
  nextF     (comp-IS m₁ m₂) r rewrite nextF m₁ (ResponseF m₂ r) | nextF m₂ r  = refl 

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₂ sf → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  _∘′-IS_ = flip comp-IS

TensorUnit-IS : InteractionStructure Empty 
Command  TensorUnit-IS  empty  = ⊥
Response TensorUnit-IS {empty} ()
next     TensorUnit-IS {empty} ()

module _ {S}(IS : IStruct S)(s : BTAll′ S) where
  TensorUnit-incl : ISMorphism TensorUnit-IS IS (const s)
  CommandF  TensorUnit-incl {empty}  ()
  ResponseF TensorUnit-incl {empty} {()}
  nextF     TensorUnit-incl {empty} {()}

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂) where
  BinTensor-IS : InteractionStructure (S₁ △ S₂)
  Command  BinTensor-IS (s₁ ▵ s₂) = Command IS₁ s₁ ⊎ Command IS₂ s₂
  Response BinTensor-IS {s₁ ▵ s₂} (left  c) = Response IS₁ c
  Response BinTensor-IS {s₁ ▵ s₂} (right c) = Response IS₂ c
  next     BinTensor-IS {s₁ ▵ s₂} (left  c) r = next IS₁ c r ▵ s₂
  next     BinTensor-IS {s₁ ▵ s₂} (right c) r = s₁ ▵ next IS₂ c r

  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure (S₁ △ S₂)
  _⊕-IS_ = BinTensor-IS

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂} where
  IncL-IS : (s₂ : BTAll′ S₂) → ISMorphism IS₁ (BinTensor-IS IS₁ IS₂) λ s₁ → s₁ ▵ s₂
  CommandF   (IncL-IS s₂) c = left c
  ResponseF  (IncL-IS s₂) r = r
  nextF      (IncL-IS s₂) r = refl

  IncR-IS : (s₁ : BTAll′ S₁) → ISMorphism IS₂ (BinTensor-IS IS₁ IS₂) λ s₂ → s₁ ▵ s₂
  CommandF   (IncR-IS s₁) c = right c
  ResponseF  (IncR-IS s₁) r = r
  nextF      (IncR-IS s₁) r = refl

module _ {S₁ S₂ T₁ T₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{JS₁ : IStruct T₁}{JS₂ : IStruct T₂}{f g} where
  binmap-IS : ISMorphism IS₁ JS₁ f → ISMorphism IS₂ JS₂ g → ISMorphism (IS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂) (f ***-BT′ g)
  CommandF  (binmap-IS m₁ m₂) {s₁ ▵ s₂} (left  c)   = left  $ CommandF m₁ c
  CommandF  (binmap-IS m₁ m₂) {s₁ ▵ s₂} (right c)   = right $ CommandF m₂ c
  ResponseF (binmap-IS m₁ m₂) {s₁ ▵ s₂} {left  c} r = ResponseF m₁ r
  ResponseF (binmap-IS m₁ m₂) {s₁ ▵ s₂} {right c} r = ResponseF m₂ r
  nextF     (binmap-IS m₁ m₂) {s₁ ▵ s₂} {left  c} r rewrite nextF m₁ r = refl
  nextF     (binmap-IS m₁ m₂) {s₁ ▵ s₂} {right c} r rewrite nextF m₂ r = refl

module _ {S T}(bf : BTAll′ S ↔ BTAll′ T)(IS : IStruct S) where
  iso-IS : IStruct T
  Command   iso-IS s = Command IS (get-inv bf s)
  Response  iso-IS c = Response IS c
  next      iso-IS {s} c r rewrite get-Ret bf (next IS c r) = get-fun bf (next IS c r)

ReplicateState-IS : ∀{l}{A : Set l} → BTree A → Nat → BTree A
ReplicateState-IS S n = foldr _△_ Empty (replicate n S)

module _ {S}(IS : IStruct S) where
  Replicate-IS : ∀ n → IStruct (ReplicateState-IS S n)
  Replicate-IS zero = TensorUnit-IS
  Replicate-IS (suc n) = BinTensor-IS IS (Replicate-IS n)
