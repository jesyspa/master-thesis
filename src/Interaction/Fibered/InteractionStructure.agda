module Interaction.Fibered.InteractionStructure where

open import ThesisPrelude
open import Algebra.Fibered.FiberedSet
open import Algebra.Proposition
open import Algebra.Equality
open import Utility.BTAll
open import Algebra.Function

record InteractionStructure (S : BTree Set) : Set₁ where
  field
    Command  : FiberedSet (BTAll′ S)
    Response : FiberedSet (total-space Command) 
    next     : total-space Response → BTAll′ S
open InteractionStructure

IStruct = InteractionStructure

record ISMorphism {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(sf : BTAll′ S₁ → BTAll′ S₂) : Set₁ where
  field
    CommandF  : RefiberingArrow sf (Command IS₁) (Command IS₂)
    ResponseF : CorefiberingArrow (total-map sf {Command IS₁} {Command IS₂} CommandF) (Response IS₂) (Response IS₁)
    nextF     : (r : total-space (Response IS₂))
              → sf (next IS₁ (total-comap sf {{!reindex (indexer (Command IS₂)) (Response IS₂)!}} {{!!}} ResponseF r)) ≡ next IS₂ r
    -- nextF     : {c : Command IS₁}(r : Response IS₂ (CommandF c)) → sf (next IS₁ c (ResponseF r)) ≡ next IS₂ (CommandF c) r 
open ISMorphism

{-
id-IS : ∀{S}{IS : IStruct S} → ISMorphism IS IS id
CommandF  id-IS = id
cmdstateF id-IS c = refl
ResponseF id-IS = id
nextF     id-IS r = refl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{sf sg} where
  comp-IS : ISMorphism IS₁ IS₂ sf → ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
  cmdstateF (comp-IS m₁ m₂) c rewrite cmdstateF m₁ c | cmdstateF m₂ (CommandF m₁ c) = refl
  ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
  nextF     (comp-IS m₁ m₂) r rewrite nextF m₁ (ResponseF m₂ r) | nextF m₂ r  = refl 

  infixr 9 _∘′-IS_
  _∘′-IS_ : ISMorphism IS₂ IS₃ sg → ISMorphism IS₁ IS₂ sf → ISMorphism IS₁ IS₃ (sg ∘′ sf)
  _∘′-IS_ = flip comp-IS

TensorUnit-IS : InteractionStructure Empty 
Command  TensorUnit-IS = ⊥
cmdstate TensorUnit-IS ()
Response TensorUnit-IS ()
next     TensorUnit-IS ()

module _ {S}(IS : IStruct S)(s : BTAll′ S) where
  TensorUnit-incl : ISMorphism TensorUnit-IS IS (const s)
  CommandF  TensorUnit-incl ()
  cmdstateF TensorUnit-incl ()
  ResponseF TensorUnit-incl {()}
  nextF     TensorUnit-incl {()}

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂) where
  BinTensor-IS : InteractionStructure (S₁ △ S₂)
  Command  BinTensor-IS = (Command IS₁ × BTAll′ S₂) ⊎ (BTAll′ S₁ × Command IS₂)
  cmdstate BinTensor-IS (left  (c , bt)) = cmdstate IS₁ c ▵ bt
  cmdstate BinTensor-IS (right (bt , c)) = bt ▵ cmdstate IS₂ c
  Response BinTensor-IS (left  (c , bt)) = Response IS₁ c
  Response BinTensor-IS (right (bt , c)) = Response IS₂ c
  next     BinTensor-IS (left  (c , bt)) r = next IS₁ c r ▵ bt
  next     BinTensor-IS (right (bt , c)) r = bt ▵ next IS₂ c r

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
