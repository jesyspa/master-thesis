module Algebra.Fibered.FiberedSet where

open import ThesisPrelude

FiberedSet : Set → Set₁
FiberedSet I = Σ Set λ A → (A → I)

module _ {I J}(ri : I → J) where
  RefiberingArrow : FiberedSet I → FiberedSet J → Set
  RefiberingArrow (A , f) (B , g) = Σ (A → B) λ s → ∀ a → ri (f a) ≡ g (s a)

module _ {I J K}{ri : I → J}{rj : J → K} where
  comp-RA : ∀{X Y Z} → RefiberingArrow ri X Y → RefiberingArrow rj Y Z → RefiberingArrow (rj ∘′ ri) X Z 
  comp-RA {A , f} {B , g} {C , h} (s , eqs) (t , eqt) = t ∘′ s , λ a → cong rj (eqs a) ⟨≡⟩ eqt (s a)

module _ {I} where
  id-RA : ∀{X : FiberedSet I} → RefiberingArrow id X X
  id-RA {A , f} = id , λ a → refl

  FiberedArrow : FiberedSet I → FiberedSet I → Set
  FiberedArrow = RefiberingArrow id
    
  _→ᶠ_ : FiberedSet I → FiberedSet I → Set
  _→ᶠ_ = FiberedArrow
  
  _∘ᶠ_ : ∀{X Y Z} → FiberedArrow Y Z → FiberedArrow X Y → FiberedArrow X Z
  _∘ᶠ_ {X} {Y} {Z} ff fg = comp-RA {X = X} {Y} {Z} fg ff

module _ {I J}(ri : I → J) where
  reindex : FiberedSet I → FiberedSet J
  reindex (A , f) = A , ri ∘′ f

  embed-reindexed : ∀{X} → RefiberingArrow ri X (reindex X)
  embed-reindexed {A , f} = id , λ a → refl

  module _ {K}(rj : J → K) where
    lift-reindexed : ∀{X Y} → RefiberingArrow rj (reindex X) Y → RefiberingArrow (rj ∘′ ri) X Y
    lift-reindexed {A , f} {B , g} ra = ra

    colift-reindexed : ∀{X Y}→ RefiberingArrow (rj ∘′ ri) X Y → RefiberingArrow rj (reindex X) Y 
    colift-reindexed {A , f} {B , g} ra = ra
