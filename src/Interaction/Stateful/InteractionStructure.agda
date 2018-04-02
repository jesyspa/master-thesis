{-# OPTIONS --allow-unsolved-metas #-}
module Interaction.Stateful.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Equality
open import Algebra.FunExt

record InteractionStructure : Set₁ where
  field
    State       : Set
    Command     : State → Set
    Response    : {s : State} → Command s → Set
    next        : {s : State}{c : Command s}(r : Response c) → State
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    StateF    : State IS₂ → State IS₁
    CommandF  : ∀{s} → Command IS₁ (StateF s) → Command IS₂ s
    ResponseF : ∀{s}{c : Command IS₁ (StateF s)} → Response IS₂ (CommandF c) → Response IS₁ c
    nextF     : ∀{s}{c : Command IS₁ (StateF s)}(r : Response IS₂ (CommandF c))
              → StateF (next IS₂ r) ≡ next IS₁ (ResponseF r)
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
StateF    id-IS = id
CommandF  id-IS = id
ResponseF id-IS = id
nextF     id-IS r = refl

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
StateF    (comp-IS m₁ m₂) = StateF m₁ ∘′ StateF m₂
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂
nextF     (comp-IS m₁ m₂) r rewrite nextF m₂ r | nextF m₁ (ResponseF m₂ r) = refl

infixr 9 _∘′-IS_
_∘′-IS_ : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
_∘′-IS_ = flip comp-IS

Zero-IS : InteractionStructure
State    Zero-IS = ⊤
Command  Zero-IS tt = ⊥
Response Zero-IS ()
next     Zero-IS {tt} {()}

⊥-IS = Zero-IS

init-IS : ∀{IS} → ISMorphism Zero-IS IS
StateF    init-IS _ = tt
CommandF  init-IS ()
ResponseF init-IS {_} {()}
nextF     init-IS {_} {()} _

Unit-IS : InteractionStructure
State    Unit-IS = ⊥
Command  Unit-IS ()
Response Unit-IS {()}
next     Unit-IS {()}

⊤-IS = Unit-IS

term-IS : ∀{IS} → ISMorphism IS Unit-IS
StateF    term-IS ()
CommandF  term-IS {()}
ResponseF term-IS {()}
nextF     term-IS {()}

module _ {A : Set}{{_ : Eq A}}(ISf : A → InteractionStructure) where
  private
    Coproduct-IS-nextHelper : (s : (a : A) → State (ISf a))(a : A)(c : Command (ISf a) (s a))
                            → Response (ISf a) c
                            → (a′ : A)
                            → State (ISf a′)
    Coproduct-IS-nextHelper s a c r a′ with a == a′
    ... | yes refl = next (ISf a) r
    ... | no neq = s a′

  Coproduct-IS : InteractionStructure
  State    Coproduct-IS = (a : A) → State (ISf a)
  Command  Coproduct-IS s = Σ A (λ a → Command (ISf a) (s a))
  Response Coproduct-IS (a , c) = Response (ISf a) c
  next     Coproduct-IS {s} {a , c} r a′ = Coproduct-IS-nextHelper s a c r a′

  Σ-IS = Coproduct-IS
  
  Incl-IS : (a : A) → ISMorphism (ISf a) Coproduct-IS
  StateF    (Incl-IS a) s = s a
  CommandF  (Incl-IS a) c = a , c
  ResponseF (Incl-IS a) r = r
  nextF     (Incl-IS a) r with a == a
  ... | yes refl = refl
  ... | no neq = ⊥-elim (neq refl) 
  

  module _ {IS}(mf : ∀ a → ISMorphism (ISf a) IS) where
    private
      Match-IS-StateHelper : State IS → State Coproduct-IS
      Match-IS-StateHelper s a = StateF (mf a) s

    Match-IS : ISMorphism Coproduct-IS IS
    StateF    Match-IS s = Match-IS-StateHelper s
    CommandF  (Match-IS) {s} (a , c) = CommandF (mf a) c
    ResponseF (Match-IS) {s} {a , c} r = ResponseF (mf a) r
    nextF     (Match-IS) {s} {a , c} r = {!fun-ext ? ? ?!} -- might not be provable

  Product-IS : InteractionStructure
  State    Product-IS = Σ A λ a → State (ISf a)
  Command  Product-IS (a , s) = Command (ISf a) s
  Response Product-IS {a , s} c = Response (ISf a) c
  next     Product-IS {a , s} r = a , next (ISf a) r

  Proj-IS : (a : A) → ISMorphism Product-IS (ISf a)
  StateF    (Proj-IS a) s = a , s
  CommandF  (Proj-IS a) c = c
  ResponseF (Proj-IS a) r = r
  nextF     (Proj-IS a) r = refl

  Pair-IS : ∀{IS}(mf : ∀ a → ISMorphism IS (ISf a)) → ISMorphism IS Product-IS
  StateF    (Pair-IS mf) (a , s) = StateF (mf a) s
  CommandF  (Pair-IS mf) {a , s} c = CommandF (mf a) c
  ResponseF (Pair-IS mf) {a , s} r = ResponseF (mf a) r
  nextF     (Pair-IS mf) {a , s} r rewrite nextF (mf a) r = refl

module _ (IS₁ IS₂ : InteractionStructure) where
  private
    bincase : Bool → InteractionStructure
    bincase false = IS₁
    bincase true  = IS₂

  BinCoproduct-IS : InteractionStructure
  BinCoproduct-IS = Coproduct-IS bincase

  infixr 2 _⊎-IS_
  _⊎-IS_ = BinCoproduct-IS

  InclL-IS : ISMorphism IS₁ BinCoproduct-IS
  InclL-IS = Incl-IS bincase false

  InclR-IS : ISMorphism IS₂ BinCoproduct-IS
  InclR-IS = Incl-IS bincase true

  BinMatch-IS : ∀{IS} → ISMorphism IS₁ IS → ISMorphism IS₂ IS → ISMorphism BinCoproduct-IS IS
  BinMatch-IS {IS} m₁ m₂ = Match-IS bincase λ { false → m₁ ; true → m₂ }

  BinProduct-IS : InteractionStructure
  BinProduct-IS = Product-IS bincase

  infixr 3 _×-IS_
  _×-IS_ = BinProduct-IS

  ProjL-IS : ISMorphism BinProduct-IS IS₁
  ProjL-IS = Proj-IS bincase false

  ProjR-IS : ISMorphism BinProduct-IS IS₂
  ProjR-IS = Proj-IS bincase true

  BinPair-IS : ∀{IS} → ISMorphism IS IS₁ → ISMorphism IS IS₂ → ISMorphism IS BinProduct-IS
  BinPair-IS {IS} m₁ m₂ = Pair-IS bincase λ { false → m₁ ; true → m₂ }

module _ {IS} where
  Codiagonal-IS : ISMorphism (IS ⊎-IS IS) IS
  Codiagonal-IS = BinMatch-IS _ _ id-IS id-IS

module _ {ISA₁ ISB₁ ISA₂ ISB₂} where
  BinJoin-IS : ISMorphism ISA₁ ISA₂ → ISMorphism ISB₁ ISB₂ → ISMorphism (ISA₁ ⊎-IS ISB₁) (ISA₂ ⊎-IS ISB₂)
  BinJoin-IS mA mB = BinMatch-IS _ _ (InclL-IS _ _ ∘′-IS mA) (InclR-IS _ _ ∘′-IS mB)

BinCoproduct*-IS : List InteractionStructure → InteractionStructure
BinCoproduct*-IS = foldr BinCoproduct-IS Zero-IS

Extend*-IS : InteractionStructure → List InteractionStructure → InteractionStructure
Extend*-IS IS ISs = IS ⊎-IS BinCoproduct*-IS ISs

Reassoc-Coproduct-IS : ∀{ISA ISB ISC} → ISMorphism (ISA ⊎-IS ISB ⊎-IS ISC) ((ISA ⊎-IS ISB) ⊎-IS ISC)
Reassoc-Coproduct-IS = BinMatch-IS _ _
                                   (comp-IS (InclL-IS _ _) (InclL-IS _ _))
                                   (BinMatch-IS _ _
                                                (comp-IS (InclR-IS _ _) (InclL-IS _ _))
                                                (InclR-IS _ _))
Reassoc′-Coproduct-IS : ∀{ISA ISB ISC} → ISMorphism ((ISA ⊎-IS ISB) ⊎-IS ISC) (ISA ⊎-IS ISB ⊎-IS ISC)
Reassoc′-Coproduct-IS = BinMatch-IS _ _
                                    (BinMatch-IS _ _
                                                 (InclL-IS _ _)
                                                 (comp-IS (InclL-IS _ _) (InclR-IS _ _)))
                                    (comp-IS (InclR-IS _ _) (InclR-IS _ _))

Commute-Coproduct-IS : ∀{ISA ISB} → ISMorphism (ISA ⊎-IS ISB) (ISB ⊎-IS ISA)
Commute-Coproduct-IS = BinMatch-IS _ _ (InclR-IS _ _) (InclL-IS _ _)

Coproduct-RightUnit-IS : ∀{IS} → ISMorphism (IS ⊎-IS ⊥-IS) IS
Coproduct-RightUnit-IS = BinMatch-IS _ _ id-IS init-IS


