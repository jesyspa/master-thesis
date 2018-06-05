module Interaction.Indexed.QuotientTensor where

open import ThesisPrelude
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.Implementation 
open import Utility.BTAll

open InteractionStructure
open ISMorphism

module _ {S₁ S₂}(IS : IStruct (S₁ △ S₂))(JS : IStruct S₂) where
  QuotientTensor-IS : InteractionStructure (S₁ △ S₂)
  Command   QuotientTensor-IS (s₁ ▵ s₂) = Command IS (s₁ ▵ s₂) ⊎ Command JS s₂
  Response  QuotientTensor-IS {s₁ ▵ s₂} (left  c) = Response IS c
  Response  QuotientTensor-IS {s₁ ▵ s₂} (right c) = Response JS c
  next      QuotientTensor-IS {s₁ ▵ s₂} (left  c) r = next IS c r
  next      QuotientTensor-IS {s₁ ▵ s₂} (right c) r = s₁ ▵ next JS c r

module _ {S₁ S₂}{IS : IStruct (S₁ △ S₂)}{JS : IStruct S₂} where
  QMatch-IS : ∀{S₃}{KS : IStruct S₃}{StateF}
            → ISMorphism IS KS (StateF ∘′ snd-BT′)
            → ISMorphism JS KS StateF
            → ISMorphism (QuotientTensor-IS IS JS) KS (StateF ∘′ snd-BT′)
  CommandF  (QMatch-IS mi mj) {s₁ ▵ s₂} (left  c) = CommandF mi c
  CommandF  (QMatch-IS mi mj) {s₁ ▵ s₂} (right c) = CommandF mj c
  ResponseF (QMatch-IS mi mj) {s₁ ▵ s₂} {left  c} r = ResponseF mi r
  ResponseF (QMatch-IS mi mj) {s₁ ▵ s₂} {right c} r = ResponseF mj r
  nextF     (QMatch-IS mi mj) {s₁ ▵ s₂} {left  c} r rewrite nextF mi r = refl
  nextF     (QMatch-IS mi mj) {s₁ ▵ s₂} {right c} r rewrite nextF mj r = refl

  QIncL-IS : ISMorphism IS (QuotientTensor-IS IS JS) id
  CommandF   QIncL-IS {s₁ ▵ s₂}  c = left c
  ResponseF  QIncL-IS {s₁ ▵ s₂} {c} r = r
  nextF      QIncL-IS {s₁ ▵ s₂} {c} r = refl 

  QIncR-IS : ∀ s₁ → ISMorphism JS (QuotientTensor-IS IS JS) λ s₂ → s₁ ▵ s₂
  CommandF   (QIncR-IS s₁) {s₂}  c = right c
  ResponseF  (QIncR-IS s₁) {s₂} {c} r = r
  nextF      (QIncR-IS s₁) {s₂} {c} r = refl 
