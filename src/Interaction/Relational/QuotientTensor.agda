module Interaction.Indexed.QuotientTensor where

open import ThesisPrelude
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.Implementation 

open InteractionStructure
open ISMorphism

module _ {S₁ S₂}(IS : IStruct (S₁ × S₂))(JS : IStruct S₂) where
  QuotientTensor-IS : InteractionStructure (S₁ × S₂)
  Command   QuotientTensor-IS (s₁ , s₂) = Command IS (s₁ , s₂) ⊎ Command JS s₂
  Response  QuotientTensor-IS {s₁ , s₂} (left  c) = Response IS c
  Response  QuotientTensor-IS {s₁ , s₂} (right c) = Response JS c
  next      QuotientTensor-IS {s₁ , s₂} {left  c} r = next IS r
  next      QuotientTensor-IS {s₁ , s₂} {right c} r = (s₁ , next JS r)

module _ {S₁ S₂}{IS : IStruct (S₁ × S₂)}{JS : IStruct S₂} where
  QMatch-IS : ∀{S₃}{KS : IStruct S₃}{StateF}
            → ISMorphism IS KS (StateF ∘′ snd)
            → ISMorphism JS KS StateF
            → ISMorphism (QuotientTensor-IS IS JS) KS (StateF ∘′ snd)
  CommandF  (QMatch-IS mi mj) {s₁ , s₂} (left  c) = CommandF mi c
  CommandF  (QMatch-IS mi mj) {s₁ , s₂} (right c) = CommandF mj c
  ResponseF (QMatch-IS mi mj) {s₁ , s₂} {left  c} r = ResponseF mi r
  ResponseF (QMatch-IS mi mj) {s₁ , s₂} {right c} r = ResponseF mj r
  nextF     (QMatch-IS mi mj) {s₁ , s₂} {left  c} r rewrite nextF mi r = refl
  nextF     (QMatch-IS mi mj) {s₁ , s₂} {right c} r rewrite nextF mj r = refl

