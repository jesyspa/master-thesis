module Interaction.Relational.Implementation where

open import ThesisPrelude
open import Algebra.Proposition
open import Algebra.Relation
open import Algebra.Indexed.Monad
open import Algebra.Indexed.Atkey
open import Algebra.Indexed.MonadRelMorphism
open import Interaction.Relational.InteractionStructure 
open import Interaction.Relational.FreeMonad 

open InteractionStructure
open IxMonad {{...}}
open IxMonadRelMorphism

module _ {S}(IS : IStruct S){𝑺 : Set} where
  Implementation : (M : (𝑺 → Set) → 𝑺 → Set)(RS : Relation S 𝑺) → Set
  Implementation M RS = ∀{s s′}(sr : RS s s′)(c : Command IS s) → M (DepRelAtkey RS (Response IS c) (next IS)) s′

module _ {S}{IS : IStruct S}{𝑺 : Set}{M : (𝑺 → Set) → 𝑺 → Set}{{_ : IxMonad M}}{RS : Relation S 𝑺} where
  {-# TERMINATING #-}
  uprop-Impl : Implementation IS M RS → IxMonadRelMorphism (FreeMonad IS) M RS
  TermRM  (uprop-Impl impl) pf fun (Return-FM a) = returnⁱ (fun pf a)
  TermRM  (uprop-Impl impl) pf fun (Invoke-FM c cont) = impl pf c >>=ⁱ λ { (DepRelV r pf′) → TermRM (uprop-Impl impl) pf′ fun (cont r) }

module _ {S₁ S₂}(IS₁ : IStruct S₁)(IS₂ : IStruct S₂)(RS : Relation S₁ S₂) where
  SyntacticImplementation : Set
  SyntacticImplementation = Implementation IS₁ (FreeMonad IS₂) RS

SynImpl = SyntacticImplementation

module _ {S}{IS : IStruct S} where
  id-SI : SynImpl IS IS _≡_
  id-SI refl c = Invoke-FM c λ r → Return-FM (DepRelV r refl)

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{RS} where
  fmap-SynImpl-FM : (si : SynImpl IS₁ IS₂ RS) → IxMonadRelMorphism (FreeMonad IS₁) (FreeMonad IS₂)  RS
  fmap-SynImpl-FM = uprop-Impl

module _ {S₁ S₂ S₃}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{IS₃ : IStruct S₃}{R₁ R₂} where
  {-# TERMINATING #-}
  comp-SI : SynImpl IS₁ IS₂ R₁ → SynImpl IS₂ IS₃ R₂ → SynImpl IS₁ IS₃ (comp-R R₁ R₂)
  comp-SI si sj (s₁ , p₁ , p₂) c = TermRM (fmap-SynImpl-FM sj) p₂ (λ { q₂ (DepRelV r q₁) → DepRelV r (_ , q₁ , q₂) }) (si p₁ c)

  infixr 9 _∘′-SI_
  _∘′-SI_ : SynImpl IS₂ IS₃ R₂ → SynImpl IS₁ IS₂ R₁ → SynImpl IS₁ IS₃ (comp-R R₁ R₂)
  _∘′-SI_ = flip comp-SI

module _ {S₁ S₂}{IS₁ : IStruct S₁}{IS₂ : IStruct S₂}{RS}(m : ISMorphism IS₁ IS₂ RS) where
  open ISMorphism m
  fmap-IS-SynImpl : SynImpl IS₁ IS₂ RS
  fmap-IS-SynImpl pf c = Invoke-FM (CommandF pf c) λ r → Return-FM (DepRelV (ResponseF pf r) (nextF pf r))

  fmap-IS-FM : FMMorphism IS₁ IS₂ RS
  fmap-IS-FM = fmap-SynImpl-FM fmap-IS-SynImpl

module _ {S₁ S₂ T₁ T₂}
         {IS₁ : IStruct S₁}{IS₂ : IStruct S₂}
         {JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         {R₁ : Relation S₁ T₁}{R₂ : Relation S₂ T₂} where
  binmap-SI : SynImpl IS₁ JS₁ R₁ → SynImpl IS₂ JS₂ R₂ → SynImpl (BinTensor-IS IS₁ IS₂) (BinTensor-IS JS₁ JS₂) (parcomp-R R₁ R₂)
  binmap-SI si sj {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) (left  c)
    = goal 
    where lem : FreeMonad JS₁ (DepRelAtkey R₁ (Response IS₁ c) (next IS₁)) t₁
          lem = si p₁ c
          rewrap : ∀{t t′} → incL-R t t′
                 → DepRelAtkey R₁ (Response IS₁ c) (next IS₁) t
                 → DepRelAtkey (parcomp-R R₁ R₂) (Response IS₁ c) (λ r → next IS₁ r , s₂) t′
          rewrap {.ta} {ta , tb} refl at = {!!}
          goal : FreeMonad (BinTensor-IS JS₁ JS₂) (DepRelAtkey (parcomp-R R₁ R₂) (Response IS₁ c) (λ r → next IS₁ r , s₂)) (t₁ , t₂)
          -- Ergo: we are looking for a response r in a state related to next IS₁ r. 
          goal = TermRM (fmap-IS-FM IncL-IS) refl rewrap lem
-- this almost works:
--    = TermRM (fmap-IS-FM IncL-IS) refl (λ { {.t} {t , t′} refl (DepRelV r {.t} pf) → DepRelV r {{!? , ?!}} {!!} }) (si p₁ c)
  binmap-SI si sj {s₁ , s₂} {t₁ , t₂} (p₁ , p₂) (right c) = {!!}
  {-
  binmap-SI si sj {s₁ , s₂} {t₁ , t₂} pf (left  c) = TermRM (fmap-IS-FM IncL-IS) $ fmapⁱ (λ { (DepRelV x pf) → DepRelV x ? }) $ si ? c
  binmap-SI si sj {s₁ , s₂} {t₁ , t₂} pf (right c) = TermRM (fmap-IS-FM IncR-IS) $ fmapⁱ (λ { (DepRelV x pf) → DepRelV x ? }) $ sj ? c
  -}

