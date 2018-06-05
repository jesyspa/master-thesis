open import ThesisPrelude
open import Algebra.Function
open import Algebra.Indexed.Monad
module Algebra.Indexed.Coreindexing {l l′}{S : Set l}{T : Set l′}
                                    (reindex : T → S)
                                    (M : (T → Set (l ⊔ l′)) → T → Set (l ⊔ l′)){{IMM : IxMonad M}} where

open import Algebra.KanExtension reindex

open IxMonad

fmapⁱ-M   = fmapⁱ IMM
returnⁱ-M = returnⁱ IMM
_>>=ⁱ-M_  = _>>=ⁱ_ IMM

Coreindexed : (S → Set (l ⊔ l′)) → (S → Set (l ⊔ l′))
Coreindexed A t = (Ran (M (A ∘′ reindex))) t

returnⁱ-CM : ∀{A s} → A s → Coreindexed A s
returnⁱ-CM a s refl = returnⁱ-M a

bindⁱ-CM : ∀{A B s} → Coreindexed A s → (∀{s′} → A s′ → Coreindexed B s′) → Coreindexed B s
bindⁱ-CM crm f t refl = crm t refl >>=ⁱ-M λ {t′} a → f a t′ refl

fmapⁱ-CM : ∀{A B t} → (∀{t′} → A t′ → B t′) → Coreindexed A t → Coreindexed B t
fmapⁱ-CM f crm t refl = fmapⁱ-M (λ a → f a) (crm t refl)

instance
  IxMonadCoreindexed : IxMonad Coreindexed
  fmapⁱ   IxMonadCoreindexed = fmapⁱ-CM
  returnⁱ IxMonadCoreindexed = returnⁱ-CM
  _>>=ⁱ_  IxMonadCoreindexed {A} {B} {s} c f = bindⁱ-CM {A} {B} {s} c f

open import Algebra.Indexed.MonadMorphism
open IxMonadMorphism
open IxMonadComorphism

EmbedCoreindexed : IxMonadComorphism Coreindexed M reindex
RunIxMCM EmbedCoreindexed {s = t} rm = rm t refl

module _ (reindex-ret : S → T)(pf : Retraction reindex-ret of reindex) where
  ExtractCoreindexed : IxMonadComorphism M Coreindexed reindex-ret
  RunIxMCM ExtractCoreindexed {A} {s = s} m t refl rewrite sym (pf t) = fmapⁱ-M (λ {t′} a → transport A (pf t′) a ) m
