module Algebra.Fibered.FiberedSet where

open import ThesisPrelude

record FiberedSet (I : Set) : Set₁ where
  field
    {TotalSpace} : Set
    Fibration  : TotalSpace → I
open FiberedSet

record RefiberingArrow {I J}(ri : I → J)(X : FiberedSet I)(Y : FiberedSet J) : Set where
  field
    TotalMap  : TotalSpace X → TotalSpace Y
    IsFibered : ∀ x → ri (Fibration X x) ≡ Fibration Y (TotalMap x)
open RefiberingArrow
  
record CorefiberingArrow {I J}(ri : I → J)(X : FiberedSet I)(Y : FiberedSet J) : Set where
  field
    TotalComap  : (y : TotalSpace Y)(i : I) → Fibration Y y ≡ ri i → TotalSpace X
    IsCofibered : ∀ y i eq → Fibration X (TotalComap y i eq) ≡ i
open CorefiberingArrow

module _ {I J}{ri : I → J}
         {II : FiberedSet I}{JJ : FiberedSet J}
         (rii : RefiberingArrow ri II JJ) where
  FiberedRefiberingArrow : FiberedSet (TotalSpace II) → FiberedSet (TotalSpace JJ) → Set
  FiberedRefiberingArrow = RefiberingArrow (TotalMap rii)

  FiberedCorefiberingArrow : FiberedSet (TotalSpace II) → FiberedSet (TotalSpace JJ) → Set
  FiberedCorefiberingArrow = CorefiberingArrow (TotalMap rii) 

⊥-RA : ∀{I} → FiberedSet I
TotalSpace ⊥-RA = ⊥
Fibration  ⊥-RA ()

init-RA : ∀{I J}{ri : I → J}{X : FiberedSet J} → RefiberingArrow ri ⊥-RA X
TotalMap  init-RA ()
IsFibered init-RA ()

init-CRA : ∀{I J}{rj : J → I}{X : FiberedSet J} → CorefiberingArrow rj X ⊥-RA
TotalComap  init-CRA ()
IsCofibered init-CRA ()

_⊎-RA_ : ∀{I} → FiberedSet I → FiberedSet I → FiberedSet I
TotalSpace (X ⊎-RA Y) = TotalSpace X ⊎ TotalSpace Y
Fibration  (X ⊎-RA Y) (left  x) = Fibration X x
Fibration  (X ⊎-RA Y) (right y) = Fibration Y y

module _ {I J}{ri : I → J}{JJ : FiberedSet J} where
  init-FRA : ∀{X : FiberedSet (TotalSpace JJ)} → FiberedRefiberingArrow {ri = ri} {⊥-RA} {JJ} init-RA ⊥-RA X 
  TotalMap  init-FRA ()
  IsFibered init-FRA ()

  init-FCRA : ∀{X : FiberedSet (TotalSpace JJ)} → FiberedCorefiberingArrow {ri = ri} {⊥-RA} {JJ} init-RA ⊥-RA X
  TotalComap  init-FCRA _ ()
  IsCofibered init-FCRA _ ()

module _ {I J}(ri : I → J) where
  reindex : FiberedSet I → FiberedSet J
  TotalSpace (reindex X) = TotalSpace X
  Fibration  (reindex X) = ri ∘′ Fibration X

  embed-reindexed : ∀{X} → RefiberingArrow ri X (reindex X)
  TotalMap  embed-reindexed = id
  IsFibered embed-reindexed x = refl

  module _ {K}(rj : J → K) where
    lift-reindexed : ∀{X Y} → RefiberingArrow rj (reindex X) Y → RefiberingArrow (rj ∘′ ri) X Y
    TotalMap  (lift-reindexed ra) = TotalMap ra
    IsFibered (lift-reindexed ra) x = IsFibered ra x

    colift-reindexed : ∀{X Y}→ RefiberingArrow (rj ∘′ ri) X Y → RefiberingArrow rj (reindex X) Y 
    TotalMap  (colift-reindexed ra) = TotalMap ra
    IsFibered (colift-reindexed ra) x = IsFibered ra x

  coreindex : FiberedSet J → FiberedSet I
  TotalSpace (coreindex Y) = Σ I λ i → Σ (TotalSpace Y) λ y → Fibration Y y ≡ ri i 
  Fibration  (coreindex Y) (i , _) = i

module _ {I} where
  FiberedCompose : (X : FiberedSet I) → FiberedSet (TotalSpace X) → FiberedSet I
  FiberedCompose X Y = reindex (Fibration X) Y

module _ {I J K}{ri : I → J}{rj : J → K} where
  comp-RA : ∀{X Y Z} → RefiberingArrow ri X Y → RefiberingArrow rj Y Z → RefiberingArrow (rj ∘′ ri) X Z 
  TotalMap  (comp-RA ra rb) = TotalMap rb ∘′ TotalMap ra
  IsFibered (comp-RA ra rb) x rewrite IsFibered ra x | IsFibered rb (TotalMap ra x) = refl

module _ {I J K}{ri : I → J}{rj : J → K} where
  comp-CRA : ∀{X Y Z} → CorefiberingArrow ri X Y → CorefiberingArrow rj Y Z → CorefiberingArrow (rj ∘′ ri) X Z
  TotalComap  (comp-CRA ra rb) z i eq = TotalComap ra (TotalComap rb z (ri i) eq) i (IsCofibered rb z (ri i) eq)
  IsCofibered (comp-CRA ra rb) z i eq
    rewrite IsCofibered ra (TotalComap rb z (ri i) eq) i (IsCofibered rb z (ri i) eq) = refl

module _ {I} where
  id-RA : {X : FiberedSet I} → RefiberingArrow id X X
  TotalMap  id-RA = id
  IsFibered id-RA x = refl

  id-CRA : {X : FiberedSet I} → CorefiberingArrow id X X
  TotalComap  id-CRA x i refl = x
  IsCofibered id-CRA x i refl = refl

  FiberedArrow : FiberedSet I → FiberedSet I → Set
  FiberedArrow = RefiberingArrow id
    
  _→ᶠ_ : FiberedSet I → FiberedSet I → Set
  _→ᶠ_ = FiberedArrow
  
  _∘ᶠ_ : ∀{X Y Z} → FiberedArrow Y Z → FiberedArrow X Y → FiberedArrow X Z
  _∘ᶠ_ {X} {Y} {Z} ff fg = comp-RA fg ff
