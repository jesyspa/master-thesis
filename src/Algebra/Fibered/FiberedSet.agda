module Algebra.Fibered.FiberedSet where

open import ThesisPrelude

FiberedSet : Set → Set₁
FiberedSet I = Σ Set λ A → (A → I)

total-space : ∀{I} → FiberedSet I → Set
total-space = fst

indexer : ∀{I}(X : FiberedSet I) → total-space X → I
indexer = snd

module _ {I J}(ri : I → J) where
  RefiberingArrow : FiberedSet I → FiberedSet J → Set
  RefiberingArrow X Y = Σ (total-space X → total-space Y) λ s → ∀ a → ri (indexer X a) ≡ indexer Y (s a)

  total-map : ∀{X Y} → RefiberingArrow X Y → total-space X → total-space Y
  total-map = fst

module _ {I J}(rj : J → I) where
  CorefiberingArrow : FiberedSet I → FiberedSet J → Set
  CorefiberingArrow X Y = Σ (total-space X → total-space Y) λ s → ∀ a → indexer X a ≡ rj (indexer Y (s a))

  total-comap : ∀{X Y} → CorefiberingArrow X Y → total-space X → total-space Y
  total-comap = fst

module _ {I J K}{ri : I → J}{rj : J → K} where
  comp-RA : ∀{X Y Z} → RefiberingArrow ri X Y → RefiberingArrow rj Y Z → RefiberingArrow (rj ∘′ ri) X Z 
  comp-RA (s , eqs) (t , eqt) = t ∘′ s , λ a → cong rj (eqs a) ⟨≡⟩ eqt (s a)

module _ {I J K}{rj : J → I}{rk : K → J} where
  comp-CRA : ∀{X Y Z} → CorefiberingArrow rj X Y → CorefiberingArrow rk Y Z → CorefiberingArrow (rj ∘′ rk) X Z 
  comp-CRA (s , eqs) (t , eqt) = t ∘′ s , λ a → eqs a ⟨≡⟩ cong rj (eqt (s a))

module _ {I} where
  id-RA : {X : FiberedSet I} → RefiberingArrow id X X
  id-RA = id , λ a → refl

  id-CRA : {X : FiberedSet I} → CorefiberingArrow id X X
  id-CRA = id , λ a → refl

  FiberedArrow : FiberedSet I → FiberedSet I → Set
  FiberedArrow = RefiberingArrow id
    
  _→ᶠ_ : FiberedSet I → FiberedSet I → Set
  _→ᶠ_ = FiberedArrow
  
  _∘ᶠ_ : ∀{X Y Z} → FiberedArrow Y Z → FiberedArrow X Y → FiberedArrow X Z
  _∘ᶠ_ {X} {Y} {Z} ff fg = comp-RA {ri = id} {rj = id} {X = X} {Y} {Z} fg ff

module _ {I J}(ri : I → J) where
  reindex : FiberedSet I → FiberedSet J
  reindex (A , f) = A , ri ∘′ f

  embed-reindexed : ∀{X} → RefiberingArrow ri X (reindex X)
  embed-reindexed {A , f} = id , λ a → refl

  module _ {K}(rj : J → K) where
    lift-reindexed : ∀{X Y} → RefiberingArrow rj (reindex X) Y → RefiberingArrow (rj ∘′ ri) X Y
    lift-reindexed {A , f} ra = ra

    colift-reindexed : ∀{X Y}→ RefiberingArrow (rj ∘′ ri) X Y → RefiberingArrow rj (reindex X) Y 
    colift-reindexed {A , f} ra = ra

module _ {I} where
  FiberedCompose : (X : FiberedSet I) → FiberedSet (total-space X) → FiberedSet I
  FiberedCompose X Y = reindex (indexer X) Y
