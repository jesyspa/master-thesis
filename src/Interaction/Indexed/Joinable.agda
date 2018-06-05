module Interaction.Indexed.Joinable where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.Function
open import Interaction.Indexed.InteractionStructure
open import Utility.BTAll

open InteractionStructure
open ISMorphism

record Joinable {S}(IS : IStruct S) : Set₁ where
  field
    StateJ   : BTAll′ S → BTAll′ S → BTAll′ S
    IStructJ : ISMorphism (IS ⊕-IS IS) IS (uncurry-BT′ StateJ)
open Joinable

module _ {S T}{IS : IStruct S}{JS : IStruct T} where
  join-joinable-IS : Joinable IS → Joinable JS → Joinable (IS ⊕-IS JS)
  StateJ              (join-joinable-IS j₁ j₂)   (s₁ ▵ t₁)   (s₂ ▵ t₂) = StateJ j₁ s₁ s₂ ▵ StateJ j₂ t₁ t₂
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} (left  (left  c)) = left  $ CommandF (IStructJ j₁) {s₁ ▵ s₂} (left  c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} (left  (right c)) = right $ CommandF (IStructJ j₂) {t₁ ▵ t₂} (left  c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} (right (left  c)) = left  $ CommandF (IStructJ j₁) {s₁ ▵ s₂} (right c)
  CommandF  (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} (right (right c)) = right $ CommandF (IStructJ j₂) {t₁ ▵ t₂} (right c)
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {left  (left  c)} r = ResponseF (IStructJ j₁) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {left  (right c)} r = ResponseF (IStructJ j₂) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {right (left  c)} r = ResponseF (IStructJ j₁) r
  ResponseF (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {right (right c)} r = ResponseF (IStructJ j₂) r
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {left  (left  c)} r rewrite nextF (IStructJ j₁) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {left  (right c)} r rewrite nextF (IStructJ j₂) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {right (left  c)} r rewrite nextF (IStructJ j₁) r = refl
  nextF     (IStructJ (join-joinable-IS j₁ j₂)) {(s₁ ▵ t₁) ▵ (s₂ ▵ t₂)} {right (right c)} r rewrite nextF (IStructJ j₂) r = refl

{- This would be a nice lemma to have and it is obviously true, but this is terrible.
module _ {S T}(bf : S ↔ T)(IS : IStruct S) where
  iso-Joinable : Joinable IS → Joinable (iso-IS bf IS)
  StateJ   (iso-Joinable j) t₁ t₂ = get-fun bf (StateJ j (get-inv bf t₁) (get-inv bf t₂))
  CommandF  (IStructJ (iso-Joinable j)) {t₁ , t₂} c
    rewrite sym $ get-Ret bf (StateJ j (get-inv bf t₁) (get-inv bf t₂))
    = CommandF (IStructJ j) {get-inv bf t₁ , get-inv bf t₂} c
  ResponseF (IStructJ (iso-Joinable j)) {t₁ , t₂} {left c} r
    rewrite sym $ get-Ret bf (StateJ j (get-inv bf t₁) (get-inv bf t₂))
    = ResponseF (IStructJ j) r
  ResponseF (IStructJ (iso-Joinable j)) {t₁ , t₂} {right c} r
    rewrite sym $ get-Ret bf (StateJ j (get-inv bf t₁) (get-inv bf t₂))
    = ResponseF (IStructJ j) r
  nextF     (IStructJ (iso-Joinable j)) {t₁ , t₂} {c} r
    = {!!}

-}

module _ {S}(IS : IStruct S)(unit : BTAll′ S)(j : Joinable IS) where
  NestedStateJoin : ∀ n → BTAll′ (ReplicateState-IS S n) → BTAll′ S
  NestedStateJoin zero = const unit
  -- weird way to write it, but it makes the latter stuff easier
  NestedStateJoin (suc n) = uncurry-BT′ (StateJ j) ∘′ (id ***-BT′ NestedStateJoin n)

  NestedJoin : ∀ n → ISMorphism (Replicate-IS IS n) IS (NestedStateJoin n)
  NestedJoin zero = TensorUnit-incl IS unit
  NestedJoin (suc n) = IStructJ j ∘′-IS binmap-IS id-IS (NestedJoin n)
