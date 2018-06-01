open import ThesisPrelude
open import Algebra.Function
open import Algebra.Indexed.Monad
module Algebra.Indexed.Reindexing {l l′}{S : Set l}{T : Set l′}
                                  (reindex : T → S)
                                  (M : (S → Set (l ⊔ l′)) → S → Set (l ⊔ l′)){{IMM : IxMonad M}} where

open import Algebra.KanExtension reindex

open IxMonad

fmapⁱ-M   = fmapⁱ IMM
returnⁱ-M = returnⁱ IMM
_>>=ⁱ-M_  = _>>=ⁱ_ IMM

Reindexed : (T → Set (l ⊔ l′)) → (T → Set (l ⊔ l′))
Reindexed A t = M (Lan A) (reindex t)

returnⁱ-RM : ∀{A t} → A t → Reindexed A t
returnⁱ-RM a = returnⁱ-M (_ , refl , a)

bindⁱ-RM : ∀{A B t} → Reindexed A t → (∀{t′} → A t′ → Reindexed B t′) → Reindexed B t
bindⁱ-RM rm f = rm >>=ⁱ-M λ { (t′ , refl , a) → f a }

fmapⁱ-RM : ∀{A B t} → (∀{t′} → A t′ → B t′) → Reindexed A t → Reindexed B t
fmapⁱ-RM f rm = fmapⁱ-M (λ { (t′ , eq , a) → t′ , eq , f a }) rm

open import Algebra.Indexed.MonadMorphism
open IxMonadMorphism
open IxMonadComorphism

EmbedReindexed : IxMonadMorphism Reindexed M reindex
RunIxMM   EmbedReindexed rm = fmapⁱ-M (λ { (s′ , refl , a) → a }) rm

module _ (reindex-sec : S → T)(pf : Section reindex-sec of reindex) where
  ExtractReindexed : IxMonadMorphism M Reindexed reindex-sec
  RunIxMM  ExtractReindexed {A} {s} m rewrite sym (pf s) = fmapⁱ-M (λ {s′} a → _ , sym (pf s′) , a) m

instance
  IxMonadReindexed : IxMonad Reindexed
  fmapⁱ   IxMonadReindexed = fmapⁱ-RM
  returnⁱ IxMonadReindexed = returnⁱ-RM
  _>>=ⁱ_  IxMonadReindexed = bindⁱ-RM
