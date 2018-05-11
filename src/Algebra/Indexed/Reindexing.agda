open import ThesisPrelude
module Algebra.Indexed.Reindexing {l l′}{S S′ : Set l}(reindex : S → S′)(M : (S → Set l′) → S → Set l′) where

-- I think this is simply impossible.
Reindexed : (S′ → Set l′) → (S′ → Set l′)
Reindexed A s′ = M (A ∘′ reindex) {!!}



