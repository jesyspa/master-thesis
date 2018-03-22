module Interaction.Structure where

open import ThesisPrelude

record InteractionStructure : Set₁ where
  field
    State : Set
    Command : State → Set
    Response : (s : State) → Command s → Set
    next : (s : State)(c : Command s)(r : Response s c) → State

module _ where
  open InteractionStructure
  IsProposition : Set → Set
  IsProposition A = (a₁ a₂ : A) → a₁ ≡ a₂

  record ISMorphism (IS₁ IS₂ : InteractionStructure)  : Set₁ where
    field
      StateF : State IS₁ → State IS₂
      MappedCommand : ∀{s} → Command IS₁ s → Set
      MappedCommandProp : ∀{s} → (c : Command IS₁ s) → IsProposition (MappedCommand c)
      MappedCommandDec : ∀{s} → (c : Command IS₁ s) → Dec (MappedCommand c)
      CommandF : ∀{s}(c : Command IS₁ s){{_ : MappedCommand c}} → Command IS₂ (StateF s)
      ResponseF : ∀{s c} → Response IS₁ s c → {{_ : MappedCommand c}} → Response IS₂ (StateF s) (CommandF c)
      nextF : ∀ s c r {{_ : MappedCommand c}} → StateF (next IS₁ s c r) ≡ next IS₂ (StateF s) (CommandF c) (ResponseF r)
      unmappedF : ∀ s c r {{_ : ¬ (MappedCommand c)}} → StateF (next IS₁ s c r) ≡ StateF s
  open ISMorphism

  id-IS : ∀{IS} → ISMorphism IS IS
  StateF id-IS = id
  MappedCommand id-IS c = ⊤
  MappedCommandProp id-IS c = λ a₁ a₂ → refl
  MappedCommandDec id-IS c = yes tt
  CommandF id-IS c = c
  ResponseF id-IS r = r
  nextF id-IS s c r = refl
  unmappedF id-IS s c r {{z}} = ⊥-elim (z tt)

  comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
  StateF (comp-IS m₁ m₂) = StateF m₂ ∘′ StateF m₁
  MappedCommand (comp-IS m₁ m₂) c = Σ (MappedCommand m₁ c) λ p → MappedCommand m₂ (CommandF m₁ c {{p}})
  MappedCommandProp (comp-IS m₁ m₂) c (ma₁ , mb₁) (ma₂ , mb₂)
    rewrite MappedCommandProp m₁ c ma₁ ma₂ | MappedCommandProp m₂ (CommandF m₁ c {{ma₂}}) mb₂ mb₁ = refl
  MappedCommandDec (comp-IS m₁ m₂) c with MappedCommandDec m₁ c
  ... | no np = no λ { (p₁ , _) → np p₁ }
  ... | yes p with MappedCommandDec m₂ (CommandF m₁ c {{p}})
  ...         | no np = no λ { (p₁ , p₂) → np (transport (λ p′ → MappedCommand m₂ (CommandF m₁ c {{p′}})) (MappedCommandProp m₁ c p₁ p) p₂) }
  ...         | yes p′ = yes (p , p′)
  CommandF (comp-IS m₁ m₂) c {{(p₁ , p₂)}} = CommandF m₂ (CommandF m₁ c {{p₁}}) {{p₂}}
  ResponseF (comp-IS m₁ m₂) r {{(p₁ , p₂)}} = ResponseF m₂ (ResponseF m₁ r {{p₁}}) {{p₂}} 
  nextF (comp-IS m₁ m₂) s c r {{(p₁ , p₂)}}
    rewrite nextF m₁ s c r {{p₁}}
          | nextF m₂ (StateF m₁ s) (CommandF m₁ c {{p₁}}) (ResponseF m₁ r {{p₁}}) {{p₂}} = refl
  unmappedF (comp-IS m₁ m₂) s c r {{np}} with MappedCommandDec m₁ c
  ... | no np₁ rewrite unmappedF m₁ s c r {{np₁}} = refl
  ... | yes p rewrite nextF m₁ s c r {{p}} with MappedCommandDec m₂ (CommandF m₁ c {{p}})
  ...         | no np₂ = unmappedF m₂ (StateF m₁ s) (CommandF m₁ c {{p}}) (ResponseF m₁ r {{p}}) {{np₂}}
  ...         | yes p₂ = ⊥-elim (np (p , p₂)) 

  Times : (IS₁ IS₂ : InteractionStructure) → InteractionStructure
  State    (Times IS₁ IS₂) = State IS₁ × State IS₂
  Command  (Times IS₁ IS₂) (s₁ , s₂) = Either (Command IS₁ s₁) (Command IS₂ s₂) 
  Response (Times IS₁ IS₂) (s₁ , s₂) (left  c) = Response IS₁ s₁ c
  Response (Times IS₁ IS₂) (s₁ , s₂) (right c) = Response IS₂ s₂ c
  next     (Times IS₁ IS₂) (s₁ , s₂) (left  c) r = (next IS₁ s₁ c r , s₂)
  next     (Times IS₁ IS₂) (s₁ , s₂) (right c) r = (s₁ , next IS₂ s₂ c r)

  module _ (IS₁ IS₂ : InteractionStructure) where
    ISₚ = Times IS₁ IS₂
    left-P : ISMorphism ISₚ IS₁
    StateF left-P = fst
    MappedCommand left-P {s₁ , s₂} (left  x) = ⊤
    MappedCommand left-P {s₁ , s₂} (right x) = ⊥
    MappedCommandProp left-P {s₁ , s₂} (left x) a₁ a₂ = refl
    MappedCommandProp left-P {s₁ , s₂} (right x) () ()
    MappedCommandDec left-P {s₁ , s₂} (left x) = yes tt
    MappedCommandDec left-P {s₁ , s₂} (right x) = no id
    CommandF left-P {s₁ , s₂} (left x) = x
    CommandF left-P {s₁ , s₂} (right x) {{()}}
    ResponseF left-P {s₁ , s₂} {left x} r = r
    ResponseF left-P {s₁ , s₂} {right x} r {{()}}
    nextF left-P (s₁ , s₂) (left x) r = refl
    nextF left-P (s₁ , s₂) (right x) r {{()}}
    unmappedF left-P (s₁ , s₂) (left x) r {{np}} = ⊥-elim (np tt)
    unmappedF left-P (s₁ , s₂) (right x) r = refl

    match-P : ∀{IS} → ISMorphism IS₁ IS → ISMorphism IS₂ IS → ISMorphism ISₚ IS
    StateF (match-P m₁ m₂) (s₁ , s₂) = {!!}
    MappedCommand (match-P m₁ m₂) = {!!}
    MappedCommandProp (match-P m₁ m₂) = {!!}
    MappedCommandDec (match-P m₁ m₂) = {!!}
    CommandF (match-P m₁ m₂) = {!!}
    ResponseF (match-P m₁ m₂) = {!!}
    nextF (match-P m₁ m₂) = {!!}
    unmappedF (match-P m₁ m₂) = {!!}


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

embedl-FIXM : ∀{IS₁ IS₂ s₁ s₂ A} → FreeIxMonad IS₁ A s₁ → FreeIxMonad (Times IS₁ IS₂) (A ∘′ fst) (s₁ , s₂)
embedl-FIXM (Return-FIXM v) = Return-FIXM v
embedl-FIXM (Invoke-FIXM c cont) = Invoke-FIXM (left c) λ r → embedl-FIXM (cont r) 

embedr-FIXM : ∀{IS₁ IS₂ s₁ s₂ A} → FreeIxMonad IS₂ A s₂ → FreeIxMonad (Times IS₁ IS₂) (A ∘′ snd) (s₁ , s₂)
embedr-FIXM (Return-FIXM v) = Return-FIXM v
embedr-FIXM (Invoke-FIXM c cont) = Invoke-FIXM (right c) λ r → embedr-FIXM (cont r) 

