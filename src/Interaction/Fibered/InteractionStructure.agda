module Interaction.Fibered.InteractionStructure where

open import ThesisPrelude
open import Algebra.Fibered.FiberedSet
open import Algebra.Proposition
open import Algebra.Equality
open import Utility.BTAll
open import Algebra.Function

open FiberedSet
open RefiberingArrow
open CorefiberingArrow

record InteractionStructure (S : BTree Set) : Set₁ where
  field
    Command  : FiberedSet (BTAll′ S)
    Response : FiberedSet (TotalSpace Command) 
    next     : TotalSpace Response → BTAll′ S
open InteractionStructure

IStruct = InteractionStructure

record ISMorphism {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(sf : BTAll′ S₁ → BTAll′ S₂) : Set₁ where
  field
    CommandF  : RefiberingArrow sf (Command IS₁) (Command IS₂)
    ResponseF : FiberedCorefiberingArrow CommandF (Response IS₁) (Response IS₂)
    nextF     : (c : TotalSpace (Command IS₁))(r : TotalSpace (Response IS₂))
              → (eq : Fibration (Response IS₂) r ≡ TotalMap CommandF c)
              → sf (next IS₁ (TotalComap ResponseF r c eq)) ≡ next IS₂ r
open ISMorphism

id-IS : ∀{S}{IS : IStruct S} → ISMorphism IS IS id
CommandF  id-IS = id-RA
ResponseF id-IS = id-CRA
nextF     id-IS c r refl = refl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{sf sg} where
  comp-IS : ISMorphism IS₁ IS₂ sf → ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  CommandF  (comp-IS m₁ m₂) = comp-RA (CommandF m₁) (CommandF m₂)
  ResponseF (comp-IS m₁ m₂) = comp-CRA (ResponseF m₁) (ResponseF m₂)
  nextF     (comp-IS m₁ m₂) c r eq
    rewrite nextF m₁ c (TotalComap (ResponseF m₂) r (TotalMap (CommandF m₁) c) eq) (IsCofibered (ResponseF m₂) r (TotalMap (CommandF m₁) c) eq)
          | nextF m₂ (TotalMap (CommandF m₁) c) r eq
      = refl

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₂ sf → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  _∘′-IS_ = flip comp-IS

TensorUnit-IS : InteractionStructure Empty 
Command  TensorUnit-IS = ⊥-RA
Response TensorUnit-IS = ⊥-RA
next     TensorUnit-IS ()

module _ {S}(IS : IStruct S)(s : BTAll′ S) where
  TensorUnit-incl : ISMorphism TensorUnit-IS IS (const s)
  CommandF  TensorUnit-incl = init-RA
  ResponseF TensorUnit-incl = init-FCRA
  nextF     TensorUnit-incl ()

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂) where
  BinTensor-IS : InteractionStructure (S₁ △ S₂)
  Command  BinTensor-IS = coreindex fst-BT′ (Command IS₁) ⊎-RA coreindex snd-BT′ (Command IS₂) 
  Response BinTensor-IS = reindex {!!} (Response IS₁) ⊎-RA reindex {!!} (Response IS₂) 
  next     BinTensor-IS = {!!} 

{-
  infixr 3 _⊕-IS_ 
  _⊕-IS_ : InteractionStructure (S₁ △ S₂)
  _⊕-IS_ = BinTensor-IS

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂} where
  IncL-IS : (s₂ : BTAll′ S₂) → ISMorphism IS₁ (BinTensor-IS IS₁ IS₂) λ s₁ → s₁ ▵ s₂
  CommandF   (IncL-IS s₂) c = left (c , s₂)
  cmdstateF  (IncL-IS s₂) c = refl
  ResponseF  (IncL-IS s₂) r = r
  nextF      (IncL-IS s₂) r = refl

  IncR-IS : (s₁ : BTAll′ S₁) → ISMorphism IS₂ (BinTensor-IS IS₁ IS₂) λ s₂ → s₁ ▵ s₂
  CommandF   (IncR-IS s₁) c = right (s₁ , c)
  cmdstateF  (IncR-IS s₁) c = refl
  ResponseF  (IncR-IS s₁) r = r
  nextF      (IncR-IS s₁) r = refl

module _ {S₁ S₂ T₁ T₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{JS₁ : IStruct T₁}{JS₂ : IStruct T₂}{sf₁ sf₂} where
  binmap-IS : ISMorphism IS₁ JS₁ sf₁ → ISMorphism IS₂ JS₂ sf₂ → ISMorphism (IS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂) (sf₁ ***-BT′ sf₂)
  CommandF  (binmap-IS m₁ m₂) (left  (c , bt))   = left  $ CommandF m₁ c , sf₂ bt
  CommandF  (binmap-IS m₁ m₂) (right (bt , c))   = right $ sf₁ bt , CommandF m₂ c
  cmdstateF (binmap-IS m₁ m₂) (left  (c , bt)) rewrite cmdstateF m₁ c  = refl
  cmdstateF (binmap-IS m₁ m₂) (right (bt , c)) rewrite cmdstateF m₂ c  = refl
  ResponseF (binmap-IS m₁ m₂) {left  (c , bt)} r = ResponseF m₁ r
  ResponseF (binmap-IS m₁ m₂) {right (bt , c)} r = ResponseF m₂ r
  nextF     (binmap-IS m₁ m₂) {left  (c , bt)} r rewrite nextF m₁ r = refl
  nextF     (binmap-IS m₁ m₂) {right (bt , c)} r rewrite nextF m₂ r = refl

ReplicateState-IS : ∀{l}{A : Set l} → BTree A → Nat → BTree A
ReplicateState-IS S n = foldr _△_ Empty (replicate n S)

module _ {S}(IS : IStruct S) where
  Replicate-IS : ∀ n → IStruct (ReplicateState-IS S n)
  Replicate-IS zero = TensorUnit-IS
  Replicate-IS (suc n) = BinTensor-IS IS (Replicate-IS n)

-}
