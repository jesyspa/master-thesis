module Interaction.Structure where

open import ThesisPrelude
open import Algebra.Proposition

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : (s : State) → Command s → Set
    next        : (s : State)(c : Command s)(r : Response s c) → State
    nop         : (s : State) → Command s
    nopResponse : (s : State) → IsContractible (Response s (nop s))
    nopNext     : (s : State)(r : Response s (nop s)) → s ≡ next s (nop s) r

module _ where
  open InteractionStructure
  record ISMorphism (IS₁ IS₂ : InteractionStructure)  : Set₁ where
    field
      StateF    : State IS₁ → State IS₂
      CommandF  : ∀{s} → Command IS₂ (StateF s) → Command IS₁ s
      ResponseF : ∀{s c} → Response IS₁ s (CommandF c) → Response IS₂ (StateF s) c
      nextF     : ∀ s c r → StateF (next IS₁ s (CommandF c) r) ≡ next IS₂ (StateF s) c (ResponseF r)
      nopToNopF : ∀ s → nop IS₁ s ≡ CommandF (nop IS₂ (StateF s))
  open ISMorphism

  id-IS : ∀{IS} → ISMorphism IS IS
  StateF    id-IS       = id
  CommandF  id-IS c     = c
  ResponseF id-IS r     = r
  nextF     id-IS s c r = refl
  nopToNopF id-IS s     = refl

  comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
  StateF    (comp-IS m₁ m₂)    = StateF m₂    ∘′ StateF m₁
  CommandF  (comp-IS m₁ m₂)    = CommandF m₁  ∘′ CommandF m₂
  ResponseF (comp-IS m₁ m₂)    = ResponseF m₂ ∘′ ResponseF m₁
  nextF     (comp-IS m₁ m₂) s c r
    rewrite nextF m₁ s (CommandF m₂ c) r | nextF m₂ (StateF m₁ s) c (ResponseF m₁ r)
                               = refl
  nopToNopF (comp-IS m₁ m₂) s
    rewrite nopToNopF m₁ s | nopToNopF m₂ (StateF m₁ s) = refl


  Product-IS : (IS₁ IS₂ : InteractionStructure) → InteractionStructure
  State       (Product-IS IS₁ IS₂) = State IS₁ × State IS₂
  Command     (Product-IS IS₁ IS₂) (s₁ , s₂) = Command IS₁ s₁ × Command IS₂ s₂ 
  Response    (Product-IS IS₁ IS₂) (s₁ , s₂) (c₁ , c₂) = Response IS₁ s₁ c₁ × Response IS₂ s₂ c₂
  next        (Product-IS IS₁ IS₂) (s₁ , s₂) (c₁ , c₂) (r₁ , r₂) = (next IS₁ s₁ c₁ r₁ , next IS₂ s₂ c₂ r₂)
  nop         (Product-IS IS₁ IS₂) (s₁ , s₂) = nop IS₁ s₁ , nop IS₂ s₂
  nopResponse (Product-IS IS₁ IS₂) (s₁ , s₂) = product-contractible (nopResponse IS₁ s₁) (nopResponse IS₂ s₂) 
  nopNext     (Product-IS IS₁ IS₂) (s₁ , s₂) (r₁ , r₂) = cong₂ _,_ (nopNext IS₁ s₁ r₁) (nopNext IS₂ s₂ r₂)

  Sum-IS : (IS₁ IS₂ : InteractionStructure) → InteractionStructure
  State       (Sum-IS IS₁ IS₂) = Either (State IS₁) (State IS₂)
  Command     (Sum-IS IS₁ IS₂) (left  s) = Command IS₁ s
  Command     (Sum-IS IS₁ IS₂) (right s) = Command IS₂ s
  Response    (Sum-IS IS₁ IS₂) (left  s) c = Response IS₁ s c
  Response    (Sum-IS IS₁ IS₂) (right s) c = Response IS₂ s c
  next        (Sum-IS IS₁ IS₂) (left  s) c r = left (next IS₁ s c r)
  next        (Sum-IS IS₁ IS₂) (right s) c r = right (next IS₂ s c r)
  nop         (Sum-IS IS₁ IS₂) (left  s) = nop IS₁ s
  nop         (Sum-IS IS₁ IS₂) (right s) = nop IS₂ s
  nopResponse (Sum-IS IS₁ IS₂) (left  s) = nopResponse IS₁ s
  nopResponse (Sum-IS IS₁ IS₂) (right s) = nopResponse IS₂ s
  nopNext     (Sum-IS IS₁ IS₂) (left  s) r = cong left  (nopNext IS₁ s r)
  nopNext     (Sum-IS IS₁ IS₂) (right s) r = cong right (nopNext IS₂ s r)
  

  module _ (IS₁ IS₂ : InteractionStructure) where
    ISₚ = Product-IS IS₁ IS₂
    left-P : ISMorphism ISₚ IS₁
    StateF    left-P = fst
    CommandF  left-P {s₁ , s₂} c = (c , nop IS₂ s₂)
    ResponseF left-P = {!!}
    nextF     left-P = {!!}
    nopToNopF left-P = {!!}

{-
    pair-P : ∀{IS} → ISMorphism IS IS₁ → ISMorphism IS IS₂ → ISMorphism IS ISₚ
    StateF    (pair-P m₁ m₂) s = StateF m₁ s , StateF m₂ s
    CommandF  (pair-P m₁ m₂) c = CommandF m₁ c , CommandF m₂ c
    ResponseF (pair-P m₁ m₂) r = ResponseF m₁ r , ResponseF m₂ r
    nextF     (pair-P m₁ m₂) s c r rewrite nextF m₁ s c r | nextF m₂ s c r = refl
    nopToNopF (pair-P m₁ m₂) s rewrite nopToNopF m₁ s | nopToNopF m₂ s = refl

    ISₛ = Sum-IS IS₁ IS₂
    left-S : ISMorphism IS₁ ISₛ
    StateF    left-S = left
    CommandF  left-S = id
    ResponseF left-S = id
    nextF     left-S s c r = refl
    nopToNopF left-S s = refl

    match-S : ∀{IS} → ISMorphism IS₁ IS → ISMorphism IS₂ IS → ISMorphism ISₛ IS
    StateF    (match-S m₁ m₂) (left  s) = StateF m₁ s
    StateF    (match-S m₁ m₂) (right s) = StateF m₂ s
    CommandF  (match-S m₁ m₂) {left  s} c = CommandF m₁ c
    CommandF  (match-S m₁ m₂) {right s} c = CommandF m₂ c
    ResponseF (match-S m₁ m₂) {left  s} r = ResponseF m₁ r
    ResponseF (match-S m₁ m₂) {right s} r = ResponseF m₂ r
    nextF     (match-S m₁ m₂) (left  s) c r = nextF m₁ s c r
    nextF     (match-S m₁ m₂) (right s) c r = nextF m₂ s c r
    nopToNopF (match-S m₁ m₂) (left  s) = nopToNopF m₁ s
    nopToNopF (match-S m₁ m₂) (right s) = nopToNopF m₂ s
    
module _ where
  open InteractionStructure
  open ISMorphism
  ISₜ : InteractionStructure
  State ISₜ          = ⊤
  Command ISₜ tt     = ⊤
  Response ISₜ tt tt = ⊤
  next ISₜ tt tt tt  = tt
  nop ISₜ tt         = tt
  nopResponse ISₜ tt = tt , λ { tt → refl }
  nopNext ISₜ tt tt  = refl

  map-T : ∀{IS} → ISMorphism IS ISₜ
  StateF    map-T _ = tt
  CommandF  map-T _ = tt
  ResponseF map-T _ = tt
  nextF     map-T _ _ _ = refl
  nopToNopF map-T _ = refl

  ISᵢ : InteractionStructure
  State ISᵢ          = ⊥
  Command ISᵢ ()
  Response ISᵢ ()
  next ISᵢ ()
  nop ISᵢ ()
  nopResponse ISᵢ ()
  nopNext ISᵢ ()

  map-I : ∀{IS} → ISMorphism ISᵢ IS
  StateF    map-I ()
  CommandF  map-I {()}
  ResponseF map-I {()} 
  nextF     map-I ()
  nopToNopF map-I ()

module _ (IS : InteractionStructure) where
  open InteractionStructure IS

  IxSet : Set₁
  IxSet = State → Set
  data FreeIxMonad : IxSet → IxSet where
    Return-FIXM : ∀{A s} → A s → FreeIxMonad A s
    Invoke-FIXM : ∀{A s} → (c : Command s) → ((r : Response s c) → FreeIxMonad A (next s c r)) → FreeIxMonad A s

  ixbind-FIXM : ∀{A B s} → FreeIxMonad A s → (∀{s′} → A s′ → FreeIxMonad B s′) → FreeIxMonad B s
  ixbind-FIXM (Return-FIXM v) f = f v
  ixbind-FIXM (Invoke-FIXM c cont) f = Invoke-FIXM c (λ r → ixbind-FIXM (cont r) f)

  data FreeParMonad : State → State → Set → Set where
    Return-FPARM : ∀{A s} → A → FreeParMonad s s A
    Invoke-FPARM : ∀{A s s′} → (c : Command s) → ((r : Response s c) → FreeParMonad (next s c r) s′ A) → FreeParMonad s s′ A

  pbind-FPARM : ∀{A B s s′ s′′} → FreeParMonad s s′ A → (A → FreeParMonad s′ s′′ B) → FreeParMonad s s′′ B
  pbind-FPARM (Return-FPARM v) f = f v
  pbind-FPARM (Invoke-FPARM c cont) f = Invoke-FPARM c (λ r → pbind-FPARM (cont r) f)

module _ where
  open ISMorphism
  open InteractionStructure
  ISMorphism-action : ∀{IS₁ IS₂ A s}(m : ISMorphism IS₁ IS₂) → FreeIxMonad IS₁ (A ∘′ StateF m) s → FreeIxMonad IS₂ A (StateF m s)
  ISMorphism-action m (Return-FIXM x) = Return-FIXM x
  ISMorphism-action {IS₁} {IS₂} {A} {s} m (Invoke-FIXM c x) = Invoke-FIXM (CommandF m c) lem
    where
      lem : (r : Response IS₂ (StateF m s) (CommandF m c)) → FreeIxMonad IS₂ A (next IS₂ (StateF m s) (CommandF m c) r)
      lem r rewrite nextF m s c {!!} = {!!}

  ISMorphism-coaction : ∀{IS₁ IS₂ A s}(m : ISMorphism IS₁ IS₂) → FreeIxMonad IS₂ A (StateF m s) → FreeIxMonad IS₁ (A ∘′ StateF m) s
  ISMorphism-coaction m (Return-FIXM x) = Return-FIXM x
  ISMorphism-coaction {IS₁} {IS₂} {A} {s} m (Invoke-FIXM c x) = Invoke-FIXM {!!} lem
    where
      lem : (r : Response IS₁ s {!!}) → FreeIxMonad IS₁ (A ∘′ StateF m) (next IS₁ s {!!} {!!})
      lem r = {!!}

{-
embedl-FIXM : ∀{IS₁ IS₂ s₁ s₂ A} → FreeIxMonad IS₁ A s₁ → FreeIxMonad (Product-IS IS₁ IS₂) (A ∘′ fst) (s₁ , s₂)
embedl-FIXM (Return-FIXM v) = Return-FIXM v
embedl-FIXM {IS₁} {IS₂} {s₁} {s₂} (Invoke-FIXM c cont) = Invoke-FIXM (c , nop IS₂ s₂) {!!}
  where
    open InteractionStructure
    lem : {!(r : Response IS₁ s₁ !}
    lem = {!!}
    -}

{-
embedr-FIXM : ∀{IS₁ IS₂ s₁ s₂ A} → FreeIxMonad IS₂ A s₂ → FreeIxMonad (Product-IS IS₁ IS₂) (A ∘′ snd) (s₁ , s₂)
embedr-FIXM (Return-FIXM v) = Return-FIXM v
embedr-FIXM (Invoke-FIXM c cont) = Invoke-FIXM (right c) λ r → embedr-FIXM (cont r) 
-}

-}
