module Interaction.Indexed.Joinable where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.Function
open import Interaction.Indexed.InteractionStructure

open InteractionStructure
open ISMorphism

record Joinable {S}(IS : IStruct S) : Set₁ where
  field
    StateJ   : S → S → S
    IStructJ : ISMorphism (IS ⊕-IS IS) IS (uncurry StateJ)
open Joinable

module _ {S T}(IS : IStruct S)(JS : IStruct T) where
  join-joinable-IS : Joinable IS → Joinable JS → Joinable (IS ⊕-IS JS)
  StateJ              (join-joinable-IS j₁ j₂)   (s₁ , t₁)   (s₂ , t₂) = StateJ j₁ s₁ s₂ , StateJ j₂ t₁ t₂
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} (left  (left  c)) = left  $ CommandF (IStructJ j₁) {s₁ , s₂} (left  c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} (left  (right c)) = right $ CommandF (IStructJ j₂) {t₁ , t₂} (left  c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} (right (left  c)) = left  $ CommandF (IStructJ j₁) {s₁ , s₂} (right c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} (right (right c)) = right $ CommandF (IStructJ j₂) {t₁ , t₂} (right c)
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {left  (left  c)} r = ResponseF (IStructJ j₁) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {left  (right c)} r = ResponseF (IStructJ j₂) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {right (left  c)} r = ResponseF (IStructJ j₁) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {right (right c)} r = ResponseF (IStructJ j₂) r
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {left  (left  c)} r rewrite nextF (IStructJ j₁) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {left  (right c)} r rewrite nextF (IStructJ j₂) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {right (left  c)} r rewrite nextF (IStructJ j₁) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ , t₁) , (s₂ , t₂)} {right (right c)} r rewrite nextF (IStructJ j₂) r = refl
