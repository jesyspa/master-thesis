{-# OPTIONS --type-in-type #-}
module Synthetic.CSConstructs where

open import ThesisPrelude
open import Algebra.FunExt
open import Algebra.Function
open import Synthetic.CommandStructure 

open CommandStructure
open CmdMorphism
open CmdMorphismSim

module _ {C} where
  id-CS : CmdMorphism C C
  CommandF  id-CS = id
  ResponseF id-CS = id

module _ {C₁ C₂ C₃} where
  comp-CS : CmdMorphism C₁ C₂ → CmdMorphism C₂ C₃ → CmdMorphism C₁ C₃
  CommandF  (comp-CS m₁ m₂) = CommandF m₂ ∘′ CommandF m₁
  ResponseF (comp-CS m₁ m₂) = ResponseF m₁ ∘′ ResponseF m₂

  infixr 9 _∘-CS_
  _∘-CS_ = flip comp-CS

module _ {A : Set}(Cf : A → CmdStruct) where
  product-CS : CmdStruct
  Command  product-CS = ∀ a → Command (Cf a)
  Response product-CS cf = Σ A λ a → Response (Cf a) (cf a)

  Π-CS = product-CS

  coproduct-CS : CmdStruct
  Command  coproduct-CS = Σ A λ a → Command (Cf a)
  Response coproduct-CS (a , c) = Response (Cf a) c

  Σ-CS = coproduct-CS

module _ {A : Set}{Cf : A → CmdStruct} where
  proj-CS : ∀ a  → CmdMorphism (Π-CS Cf) (Cf a)
  CommandF  (proj-CS a) cf = cf a
  ResponseF (proj-CS a) r = a , r

{-
  postulate
    -- I have feeling something like this may be needed to show pair-uniq-CS.
    proj-ResponseF-Inj : ∀ a → Injective (λ r → ResponseF (proj-CS a) {{!!}} r)
    -}

  inj-CS : ∀ a  → CmdMorphism (Cf a) (Σ-CS Cf)
  CommandF  (inj-CS a) c = a , c
  ResponseF (inj-CS a) r = r

  module _ {C}(pf : ∀ a → CmdMorphism C (Cf a)) where
    pair-CS : CmdMorphism C (Π-CS Cf)
    CommandF  pair-CS c a = CommandF (pf a) c
    ResponseF pair-CS (a , r) = ResponseF (pf a) r

    pair-corr-Pred : CmdMorphism C (Π-CS Cf) → Set
    pair-corr-Pred m = ∀ a → proj-CS a ∘-CS m ≡C pf a 

    pair-corr-CS : pair-corr-Pred pair-CS
    CommandEq  (pair-corr-CS a) c = refl
    ResponseEq (pair-corr-CS a) r = refl

{-
    pair-uniq-CS : ∀ m → pair-corr-Pred m → m ≡C pair-CS
    CommandEq  (pair-uniq-CS m cor) c = dep-fun-ext _ _ λ a → CommandEq (cor a) c
    ResponseEq (pair-uniq-CS m cor) {c} (a , r) =
      ResponseF m (a , r)
        ≡⟨ {!!} ⟩
      ResponseF pair-CS (transport (Response (Π-CS Cf)) (dep-fun-ext _ _ λ a → CommandEq (cor a) c) (a , r))
      ∎
      -}

  module _ {C}(pf : ∀ a → CmdMorphism (Cf a) C) where
    match-CS : CmdMorphism (coproduct-CS Cf) C
    CommandF  match-CS (a , c) = CommandF (pf a) c
    ResponseF match-CS {a , c} r = ResponseF (pf a) r

choice : {A : Set} → A → A → Bool → A
choice a₁ a₂ false = a₁
choice a₁ a₂ true  = a₂

dep-choice : ∀{l l′}{B : Set l}{A₁ A₂ : B}(F : B → Set l′) → F A₁ → F A₂ → (b : Bool) → F (choice A₁ A₂ b)
dep-choice F a₁ a₂ false = a₁
dep-choice F a₁ a₂ true  = a₂

Σ-pair : Set → Set → Set
Σ-pair A B = Σ Bool (choice A B)

module _ C₁ C₂ where
  bincase : Bool → CmdStruct
  bincase = choice C₁ C₂

  binproduct-CS : CmdStruct
  binproduct-CS = product-CS bincase

  bincoproduct-CS : CmdStruct
  bincoproduct-CS = coproduct-CS bincase

module _ {C₁ C₂ C}(m₁ : CmdMorphism C C₁)(m₂ : CmdMorphism C C₂) where
  binpaircase : (b : Bool) → CmdMorphism C (bincase C₁ C₂ b)
  binpaircase = dep-choice (CmdMorphism C) m₁ m₂

  binpair-CS : CmdMorphism C (binproduct-CS C₁ C₂)
  binpair-CS = pair-CS binpaircase

module _ {C₁ C₂ C}(m₁ : CmdMorphism C₁ C)(m₂ : CmdMorphism C₂ C) where
  binmatchcase : (b : Bool) → CmdMorphism (bincase C₁ C₂ b) C
  binmatchcase = dep-choice (flip CmdMorphism C) m₁ m₂
          
  binmatch-CS : CmdMorphism (bincoproduct-CS C₁ C₂) C
  binmatch-CS = match-CS binmatchcase

module _ {C₁ C₂}(m₁ m₂ : CmdMorphism C₁ C₂) where
  equalizer-CS : CmdStruct
  Command  equalizer-CS = Σ (Command C₁) λ c₁ → CommandF m₁ c₁ ≡ CommandF m₂ c₁
  Response equalizer-CS (c₁ , eq) = Σ (Response C₂ (CommandF m₁ c₁)) λ r → ResponseF m₁ r ≡ ResponseF m₂ (transport (Response C₂) eq r) 

  

module _ {A C}{Cf : A → CmdStruct} where
  Cf′ : A → CmdStruct
  Cf′ a = binproduct-CS C (Cf a)
  move-in : CmdMorphism (binproduct-CS C (coproduct-CS Cf)) (coproduct-CS Cf′)
  CommandF  move-in cp with cp true
  ... | a , ca = a , dep-choice Command (cp false) ca
  ResponseF move-in {cp} (false , r) with cp true
  ... | a , ca = false , r
  ResponseF move-in {cp} (true  , r) with cp true | graphAt cp true
  ... | a , ca | ingraph refl = true  , r

  move-out : CmdMorphism (coproduct-CS Cf′) (binproduct-CS C (coproduct-CS Cf)) 
  CommandF  move-out (a , ca) = dep-choice Command (ca false) (a , ca true)
  ResponseF move-out {a , ca} (false , r) = false , r
  ResponseF move-out {a , ca} (true  , r) = true  , r

{-
-- modelling the type C₁ => C₂
-- this type bothers me, since the quantification over set is really non-avoidable it seems...
module _ C₁ C₂ where
  exp-CS : CmdStruct
  Command  exp-CS = Command C₁ → Command C₂
  -- I think the Σ (Command C₁) λ c₁ → ? part is correct, but the rest probably isn't.
  Response exp-CS cf = Σ (Command C₁) λ c₁ → {A : Set} → (Response C₂ (cf c₁) → Σ-pair A (Response C₁ c₁)) → A

module _ {C₀ C₁ C₂} where
  curry-CS : CmdMorphism (binproduct-CS C₀ C₁) C₂ → CmdMorphism C₀ (exp-CS C₁ C₂)
  CommandF  (curry-CS m) c₀ c₁ = CommandF m (dep-choice Command c₀ c₁)
  ResponseF (curry-CS m) {c₀} (c₁ , rf) = rf lem
    where lem : Response C₂ (CommandF m (dep-choice Command c₀ c₁)) → Σ-pair (Response C₀ c₀) (Response C₁ c₁)
          lem r₂ with ResponseF m r₂
          ... | false , r = false , r
          ... | true  , r = true  , r

  uncurry-CS : CmdMorphism C₀ (exp-CS C₁ C₂) → CmdMorphism (binproduct-CS C₀ C₁) C₂
  CommandF  (uncurry-CS m) c = CommandF m (c false) (c true)
  ResponseF (uncurry-CS m) {c} r = ? -- I don't think this is implementable.

-}
