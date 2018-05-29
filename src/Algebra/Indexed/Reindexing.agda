open import ThesisPrelude
open import Algebra.Function
open import Algebra.Indexed.Monad
module Algebra.Indexed.Reindexing {l l′}{S : Set l}{S′ : Set l′}
                                  (reindex : S′ → S)
                                  (M : (S → Set (l ⊔ l′)) → S → Set (l ⊔ l′)){{IMM : IxMonad M}} where

open import Algebra.KanExtension reindex

open IxMonad

fmapⁱ-M   = fmapⁱ IMM
returnⁱ-M = returnⁱ IMM
_>>=ⁱ-M_  = _>>=ⁱ_ IMM

Reindexed : (S′ → Set (l ⊔ l′)) → (S′ → Set (l ⊔ l′))
Reindexed A s′ = M (Lan A) (reindex s′)

returnⁱ-RM : ∀{A s} → A s → Reindexed A s
returnⁱ-RM a = returnⁱ-M (_ , refl , a)

bindⁱ-RM : ∀{A B s} → Reindexed A s → (∀{s′} → A s′ → Reindexed B s′) → Reindexed B s
bindⁱ-RM rm f = rm >>=ⁱ-M λ { (s′ , refl , a) → f a }

fmapⁱ-RM : ∀{A B s} → (∀{s′} → A s′ → B s′) → Reindexed A s → Reindexed B s
fmapⁱ-RM f rm = fmapⁱ-M (λ { (s′ , eq , a) → s′ , eq , f a }) rm

open import Algebra.Indexed.MonadMorphism
open IxMonadMorphism
open IxMonadComorphism

EmbedReindexed : IxMonadMorphism Reindexed M
StateM  EmbedReindexed = reindex
TermM   EmbedReindexed rm = fmapⁱ-M (λ { (s′ , refl , a) → a }) rm

