module Interaction.Indexed.Telescope where

open import ThesisPrelude
open import Algebra.Equality
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.Implementation
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.QuotientTensor

open InteractionStructure
open ISMorphism
open IxMonad {{...}}
open IxMonadMorphism

data InfcTelescope : List Set → Set₁ where
  InfcEmpty : InfcTelescope []
  InfcCons  : ∀{S Ss}(IS : IStruct (S × foldr _×_ ⊤ Ss))
         → InfcTelescope Ss
         → InfcTelescope (S ∷ Ss)

InfcTele-QT : ∀{Ss} → (tele : InfcTelescope Ss) → IStruct (foldr _×_ ⊤ Ss)
InfcTele-QT InfcEmpty = TensorUnit-IS
InfcTele-QT (InfcCons IS tele) = QuotientTensor-IS IS (InfcTele-QT tele)

data ISTelescope : List Set → Set₁ where
  ISEmpty : ISTelescope []
  ISCons  : ∀{S Ss}
          → IStruct S
          → ISTelescope Ss
          → ISTelescope (S ∷ Ss)

ISTele-T : ∀{Ss} → ISTelescope Ss → IStruct (foldr _×_ ⊤ Ss)
ISTele-T ISEmpty = TensorUnit-IS
ISTele-T (ISCons IS tele) = BinTensor-IS IS (ISTele-T tele)

data ImplTelescope : ∀{Infcs Impls}
                   → InfcTelescope Infcs
                   → ISTelescope Impls
                   → Set₁ where
  ImplEmpty : ImplTelescope InfcEmpty ISEmpty
  ImplCons  : ∀{S T Ss Ts}{IS : IStruct (S × foldr _×_ ⊤ Ss)}{JS : IStruct T}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
            → (f : S → T)
            → SynImpl IS (JS ⊕-IS InfcTele-QT ISs) (first f)
            → ImplTelescope ISs JSs
            → ImplTelescope (InfcCons IS ISs) (ISCons JS JSs)
       
module _ {S₁ S₂ T₁ T₂}{IS₁ : IStruct (S₁ × S₂)}{IS₂ : IStruct S₂}{JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         (f₁ : S₁ → T₁)(f₂ : S₂ → T₂)
         (si₁ : SynImpl IS₁ (JS₁ ⊕-IS IS₂) (first f₁))(si₂ : SynImpl IS₂ JS₂ f₂) where
  combine-bin : SynImpl (QuotientTensor-IS IS₁ IS₂) (JS₁ ⊕-IS JS₂) (f₁ ***′ f₂)
  combine-bin {s₁ , s₂} (left  c) = TermM fmm (fmapⁱ lem (si₁ c))
    where
      fmm = fmap-SynImpl-FM λ {s} → (binmap-SI {StateF₁ = id} (id-SI {IS = JS₁}) si₂) {s}
      lem : ∀{s′}
          → StrongAtkey (Response IS₁ c) (first f₁ ∘′ next IS₁) s′
          → StrongAtkey (Response IS₁ c) ((f₁ ***′ f₂) ∘′ (λ r → next IS₁ r)) (StateM fmm s′)
      lem {s₁′ , t₂′} (StrongV r eq) = StrongV r lem-eq
        where
          split-***′ : ∀ sᵢ → (f₁ ***′ f₂) sᵢ ≡ second f₂ (first f₁ sᵢ)
          split-***′ (_ , _) = refl
          lem-eq : (s₁′ , f₂ t₂′) ≡ (f₁ ***′ f₂) (next IS₁ r)
          lem-eq rewrite split-***′ (next IS₁ r) | sym eq = refl
  combine-bin {s₁ , s₂} (right c) = TermM (fmap-IS-FM (IncR-IS (f₁ s₁))) goal
    where
      lem : FreeMonad JS₂ (StrongAtkey (Response IS₂ c) (f₂ ∘′ next IS₂)) (f₂ s₂)
      lem = si₂ c
      goal : FreeMonad JS₂ (StrongAtkey (Response IS₂ c) (λ r → f₁ s₁ , f₂ (next IS₂ r)) ∘′ λ t₂ → f₁ s₁ , t₂) (f₂ s₂)
      goal = fmapⁱ (λ { (StrongV r refl) → StrongV r refl }) lem

combine-state : ∀{Ss Ts} {ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
              → ImplTelescope ISs JSs
              → foldr _×_ ⊤ Ss → foldr _×_ ⊤ Ts
combine-state ImplEmpty tt = tt
combine-state (ImplCons f si tele) = f ***′ combine-state tele

combine-tele : ∀{Ss Ts}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts} 
             → (tele : ImplTelescope ISs JSs)
             → SynImpl (InfcTele-QT ISs) (ISTele-T JSs) (combine-state tele)
combine-tele ImplEmpty ()
combine-tele (ImplCons {IS = IS} {JS} {ISs} {JSs} f si tele) {s , ss} c
  = combine-bin {IS₁ = IS} f (combine-state {ISs = ISs} {JSs} tele) si (combine-tele tele) {s , ss} c 
