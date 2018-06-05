module Interaction.Indexed.Telescope where

open import ThesisPrelude
open import Algebra.Equality
open import Algebra.Lift
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.Implementation
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.QuotientTensor
open import Utility.BTAll

open InteractionStructure
open ISMorphism
open IxMonad {{...}}
open IxMonadMorphism
open Implementation

data InfcTelescope : BTree Set → Set₁ where
  InfcEmpty : InfcTelescope Empty 
  InfcCons  : ∀{S Ss}(IS : IStruct (S △ Ss))
         → InfcTelescope Ss
         → InfcTelescope (S △ Ss)

InfcTele-QT : ∀{Ss} → (tele : InfcTelescope Ss) → IStruct Ss
InfcTele-QT InfcEmpty = TensorUnit-IS
InfcTele-QT (InfcCons IS tele) = QuotientTensor-IS IS (InfcTele-QT tele)

data ISTelescope : BTree Set → Set₁ where
  ISEmpty : ISTelescope Empty 
  ISCons  : ∀{S Ss}
          → IStruct S
          → ISTelescope Ss
          → ISTelescope (S △ Ss)

ISTele-T : ∀{Ss} → ISTelescope Ss → IStruct Ss
ISTele-T ISEmpty = TensorUnit-IS
ISTele-T (ISCons IS tele) = BinTensor-IS IS (ISTele-T tele)

data ImplTelescope : ∀{Infcs Impls}
                   → InfcTelescope Infcs
                   → ISTelescope Impls
                   → Set₁ where
  ImplEmpty : ImplTelescope InfcEmpty ISEmpty
  ImplCons  : ∀{S T Ss Ts}{IS : IStruct (S △ Ss)}{JS : IStruct T}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
            → (f : BTAll′ S → BTAll′ T)
            → SynImpl IS (JS ⊕-IS InfcTele-QT ISs) (first-BT′ f)
            → ImplTelescope ISs JSs
            → ImplTelescope (InfcCons IS ISs) (ISCons JS JSs)
       
module _ {S₁ S₂ T₁ T₂}{IS₁ : IStruct (S₁ △ S₂)}{IS₂ : IStruct S₂}{JS₁ : IStruct T₁}{JS₂ : IStruct T₂}
         (f₁ : BTAll′ S₁ → BTAll′ T₁)(f₂ : BTAll′ S₂ → BTAll′ T₂)
         (si₁ : SynImpl IS₁ (JS₁ ⊕-IS IS₂) (first-BT′ f₁))(si₂ : SynImpl IS₂ JS₂ f₂) where
  combine-bin : SynImpl (QuotientTensor-IS IS₁ IS₂) (JS₁ ⊕-IS JS₂) (f₁ ***-BT′ f₂)
  RunImpl combine-bin {s₁ ▵ s₂} (left  c) = RunIxMM fmm (fmapⁱ {s = f₁ s₁ ▵ s₂} lem (RunImpl si₁ c))
    where
      fmm : FMMorphism (JS₁ ⊕-IS IS₂) (JS₁ ⊕-IS JS₂) (id ***-BT′ f₂)
      fmm = fmap-SynImpl-FM (binmap-SI {StateF₁ = id} (id-SI {IS = JS₁}) si₂)
      lem : ∀{s′}
          → StrongAtkey (Response IS₁ c) (first-BT′ f₁ ∘′ next IS₁ c) s′
          → StrongAtkey (Response IS₁ c) ((f₁ ***-BT′ f₂) ∘′ (λ r → next IS₁ c r)) ((id ***-BT′ f₂) s′)
      lem {s₁′ ▵ t₂′} (StrongV r eq) = StrongV r lem-eq
        where
          split-***′ : ∀ sᵢ → (f₁ ***-BT′ f₂) sᵢ ≡ second-BT′ f₂ (first-BT′ f₁ sᵢ)
          split-***′ (_ ▵ _) = refl
          lem-eq : (s₁′ ▵ f₂ t₂′) ≡ (f₁ ***-BT′ f₂) (next IS₁ c r)
          lem-eq rewrite split-***′ (next IS₁ c r) | sym eq = refl
  RunImpl combine-bin {s₁ ▵ s₂} (right c) = RunIxMM (fmap-IS-FM (IncR-IS (f₁ s₁))) goal
    where
      lem : FreeMonad JS₂ (StrongAtkey (Response IS₂ c) (f₂ ∘′ next IS₂ c)) (f₂ s₂)
      lem = RunImpl si₂ c
      goal : FreeMonad JS₂ (StrongAtkey (Response IS₂ c) (λ r → f₁ s₁ ▵ f₂ (next IS₂ c r)) ∘′ λ t₂ → f₁ s₁ ▵ t₂) (f₂ s₂)
      goal = fmapⁱ (λ { (StrongV r refl) → StrongV r refl }) lem

combine-state : ∀{Ss Ts} {ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
              → ImplTelescope ISs JSs
              → BTAll′ Ss → BTAll′ Ts
combine-state ImplEmpty = id
combine-state (ImplCons f si tele) = f ***-BT′ combine-state tele

combine-tele : ∀{Ss Ts}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts} 
             → (tele : ImplTelescope ISs JSs)
             → SynImpl (InfcTele-QT ISs) (ISTele-T JSs) (combine-state tele)
combine-tele ImplEmpty = id-SI
combine-tele (ImplCons {IS = IS} {JS} {ISs} {JSs} f si tele)
  = combine-bin {IS₁ = IS} f (combine-state {ISs = ISs} {JSs} tele) si (combine-tele tele)
