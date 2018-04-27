module Interaction.Complete.InteractionStructure where

open import ThesisPrelude
open import Algebra.Proposition
open import Interaction.Complete.Elem 

record InteractionStructure : Set₁ where
  field
    Command     : Set
    Response    : Command → Set
open InteractionStructure

record ISMorphism (IS₁ IS₂ : InteractionStructure) : Set where
  field
    CommandF  : Command IS₁ → Command IS₂
    ResponseF : ∀{c} → Response IS₂ (CommandF c) → Response IS₁ c
open ISMorphism

id-IS : ∀{IS} → ISMorphism IS IS
CommandF  id-IS = id
ResponseF id-IS = id

comp-IS : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₁ IS₂ → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₃
CommandF  (comp-IS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
ResponseF (comp-IS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂

infixr 9 _∘′-IS_
_∘′-IS_ : ∀{IS₁ IS₂ IS₃} → ISMorphism IS₂ IS₃ → ISMorphism IS₁ IS₂ → ISMorphism IS₁ IS₃
_∘′-IS_ = flip comp-IS

Zero-IS : InteractionStructure
Command  Zero-IS = ⊥
Response Zero-IS ()

⊥-IS = Zero-IS

init-IS : ∀{IS} → ISMorphism Zero-IS IS
CommandF  init-IS ()
ResponseF init-IS {()}

Unit-IS : InteractionStructure
Command  Unit-IS = ⊤
Response Unit-IS tt = ⊥

⊤-IS = Unit-IS

term-IS : ∀{IS} → ISMorphism IS Unit-IS
CommandF  term-IS c = tt
ResponseF term-IS ()

module _ {A : Set}(ISf : A → InteractionStructure) where
  Coproduct-IS : InteractionStructure
  Command  Coproduct-IS = Σ A (Command ∘′ ISf)
  Response Coproduct-IS (a , c) = Response (ISf a) c

  Σ-IS = Coproduct-IS
  
  Incl-IS : (a : A) → ISMorphism (ISf a) Coproduct-IS
  CommandF  (Incl-IS a) c = a , c
  ResponseF (Incl-IS a) r = r

  Match-IS : ∀{IS}(mf : ∀ a → ISMorphism (ISf a) IS) → ISMorphism Coproduct-IS IS
  CommandF  (Match-IS mf) (a , c) = CommandF (mf a) c
  ResponseF (Match-IS mf) {a , c} r = ResponseF (mf a) r

  Product-IS : InteractionStructure
  Command  Product-IS = ∀ a → Command (ISf a)
  Response Product-IS c = Σ A λ a → Response (ISf a) (c a)

  Proj-IS : (a : A) → ISMorphism Product-IS (ISf a)
  CommandF  (Proj-IS a) c = c a
  ResponseF (Proj-IS a) r = a , r

  Pair-IS : ∀{IS}(mf : ∀ a → ISMorphism IS (ISf a)) → ISMorphism IS Product-IS
  CommandF  (Pair-IS mf) c a = CommandF (mf a) c
  ResponseF (Pair-IS mf) (a , r) = ResponseF (mf a) r

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

{-
ListCoproduct-IS : List InteractionStructure → InteractionStructure
ListCoproduct-IS xs = Coproduct-IS (getElem {lzero} ?) 

embedListCoproduct-IS : ∀{x xs} → ISMorphism (ListCoproduct-IS xs) (ListCoproduct-IS (x ∷ xs))
CommandF  embedListCoproduct-IS (p , c) = that p , c
ResponseF embedListCoproduct-IS {p , c} r = r

Bin*2List-IS : ∀{xs} → ISMorphism (BinCoproduct*-IS xs) (ListCoproduct-IS xs)
CommandF  (Bin*2List-IS {[]})     ()
CommandF  (Bin*2List-IS {x ∷ xs}) (false , c) = this x , c
CommandF  (Bin*2List-IS {x ∷ xs}) (true  , c) = CommandF (comp-IS Bin*2List-IS embedListCoproduct-IS) c 
ResponseF (Bin*2List-IS {[]})     {()}
ResponseF (Bin*2List-IS {x ∷ xs}) {false , c} r = r
ResponseF (Bin*2List-IS {x ∷ xs}) {true  , c} r = ResponseF (comp-IS (Bin*2List-IS {xs}) embedListCoproduct-IS) r 

List2Bin*-IS : ∀{xs} → ISMorphism (ListCoproduct-IS xs) (BinCoproduct*-IS xs)
CommandF  (List2Bin*-IS {[]})     (() , _)
CommandF  (List2Bin*-IS {x ∷ xs}) (this .x , c) = CommandF (InclL-IS _ _) c
CommandF  (List2Bin*-IS {x ∷ xs}) (that p  , c) = CommandF (comp-IS {!!} List2Bin*-IS) c
ResponseF (List2Bin*-IS {[]})     {() , _}
ResponseF (List2Bin*-IS {x ∷ xs}) {this .x , c} r = {!!}
ResponseF (List2Bin*-IS {x ∷ xs}) {that p  , c} r = {!!}

-}