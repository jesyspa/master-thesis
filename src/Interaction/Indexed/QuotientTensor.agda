module Interaction.Indexed.QuotientTensor where

open import ThesisPrelude
open import Interaction.Indexed.InteractionStructure 
open import Interaction.Indexed.Implementation 

open InteractionStructure
open ISMorphism

module _ {S₁ S₂}(IS : IStruct S₁)(JS : IStruct S₂)(StateF : S₁ → S₂) where
  record ISEmbedding : Set where
    field
      nextE     : ∀{s}{c : Command JS (StateF s)}(r : Response JS c) → S₁
      nextECong : ∀{s}{c : Command JS (StateF s)}(r : Response JS c) → StateF (nextE r) ≡ next JS r

open ISEmbedding

module _ {S₁ S₂}{IS : IStruct S₁}{JS : IStruct S₂}{StateF : S₁ → S₂}(emb : ISEmbedding IS JS StateF) where
  QuotientTensor-IS : InteractionStructure S₁
  Command   QuotientTensor-IS  s = Command IS s ⊎ Command JS (StateF s)
  Response  QuotientTensor-IS {s} (left  c) = Response IS c
  Response  QuotientTensor-IS {s} (right c) = Response JS c
  next      QuotientTensor-IS {s} {left  c} r = next IS r
  next      QuotientTensor-IS {s} {right c} r = nextE emb r

module _ {S₁ S₂}{IS : IStruct S₁}{JS : IStruct S₂}{StateF : S₁ → S₂}{emb : ISEmbedding IS JS StateF} where
  QMatch-IS : ∀{S₃}{KS : IStruct S₃}{StateG}
            → ISMorphism IS KS (StateG ∘′ StateF)
            → ISMorphism JS KS StateG
            → ISMorphism (QuotientTensor-IS emb) KS (StateG ∘′ StateF)
  CommandF  (QMatch-IS mi mj) {s} (left  c) = CommandF mi c
  CommandF  (QMatch-IS mi mj) {s} (right c) = CommandF mj c
  ResponseF (QMatch-IS mi mj) {s} {left  c} r = ResponseF mi r
  ResponseF (QMatch-IS mi mj) {s} {right c} r = ResponseF mj r
  nextF     (QMatch-IS mi mj) {s} {left  c} r rewrite nextF mi r = refl
  nextF     (QMatch-IS mi mj) {s} {right c} r rewrite nextECong emb (ResponseF mj r) | nextF mj r = refl

