open import ThesisPrelude using (Monad)
open import Algebra.Indexed.Monad 
open import ThesisPrelude
module Utility.State.Indexed.ReindexingTransformer {l′}{T : Set}{𝑺 : Set l′}(ev : 𝑺 → Set l′)(M : (T → Set (lsuc l′)) → (T → Set (lsuc l′))){{IMM : IxMonad M}} where

open import Algebra.Lift
open import Algebra.Indexed.Atkey 
open import Utility.State.Indexed.Transformer {lzero} {l′} M {{IMM}}

open IxMonad IMM
open import Algebra.Indexed.Reindexing {S = Set l′ × T}{T = 𝑺 × T} (first ev) IxStateT {{it}}

IxStateTᵣ : (𝑺 × T → Set (lsuc l′)) → (𝑺 × T → Set (lsuc l′))
IxStateTᵣ = Reindexed 

modifyTᵣ : ∀{S S′ t} → (ev S → ev S′) → IxStateTᵣ (Atkey (Lift (ev S′)) (S′ , t)) (S , t)
modifyTᵣ {S} {S′} {t} f s = returnⁱ (ev S′ , ((S′ , t) , refl , V (lift (f s))) , f s)

liftTᵣ : ∀{A t} S → M A t → IxStateTᵣ (A ∘′ snd) (S , t)
liftTᵣ S m s = fmapⁱ (λ {t} a → ev S , ((S , t) , refl , a) , s) m

instance
  IxMonadStateTᵣ : IxMonad IxStateTᵣ
  IxMonadStateTᵣ = IxMonadReindexed
