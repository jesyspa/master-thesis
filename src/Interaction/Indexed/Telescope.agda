module Interaction.Indexed.Telescope where

open import ThesisPrelude
open import Algebra.Indexed.Monad
open import Algebra.Indexed.MonadMorphism
open import Algebra.Indexed.Atkey
open import Interaction.Indexed.InteractionStructure
open import Interaction.Indexed.Implementation
open import Interaction.Indexed.FreeMonad
open import Interaction.Indexed.QuotientTensor

open InteractionStructure
open ISMorphism
open ISEmbedding
open IxMonad {{...}}
open IxMonadMorphism

mutual
  data InfcTelescope : List Set → Set₁ where
    InfcEmpty : InfcTelescope []
    InfcCons  : ∀{S Ss}{IS : IStruct S}
           → (tele : InfcTelescope Ss)
           → {f : S → Tele-S tele}
           → ISEmbedding IS (Tele-QT tele) f
           → InfcTelescope (S ∷ Ss)

  Tele-S : ∀{Ss} → InfcTelescope Ss → Set
  Tele-S InfcEmpty = ⊤
  Tele-S (InfcCons {S} _ _) = S

  Tele-QT : ∀{Ss} → (tele : InfcTelescope Ss) → IStruct (Tele-S tele)
  Tele-QT InfcEmpty = TensorUnit-IS
  Tele-QT (InfcCons tele emb) = QuotientTensor-IS emb

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
  ImplCons  : ∀{S T Ss Ts}{IS : IStruct S}{JS : IStruct T}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
            → {f : S → Tele-S ISs}
            → {g : S → T}
            → (emb : ISEmbedding IS (Tele-QT ISs) f)
            → SynImpl IS (JS ⊕-IS Tele-QT ISs) (g &&& f)
            → ImplTelescope ISs JSs
            → ImplTelescope (InfcCons ISs emb) (ISCons JS JSs)
       
combine-state : ∀{Ss Ts} {ISs : InfcTelescope Ss}{JSs : ISTelescope Ts}
              → ImplTelescope ISs JSs
              → Tele-S ISs → foldr _×_ ⊤ Ts
combine-state ImplEmpty s = tt
combine-state (ImplCons {f = f} {g} emb x tele) s = g s , combine-state tele (f s)

combine-tele : ∀{Ss Ts}{ISs : InfcTelescope Ss}{JSs : ISTelescope Ts} 
             → (tele : ImplTelescope ISs JSs)
             → SynImpl (Tele-QT ISs) (ISTele-T JSs) (combine-state tele)
combine-tele ImplEmpty ()
combine-tele (ImplCons emb si tele) (left  c) = {!!}
combine-tele (ImplCons {IS = IS} {JS} {ISs} {JSs} {f = f} {g} emb si tele) {s} (right c) = TermM (fmap-IS-FM (IncR-IS _)) goal
  where lem : FreeMonad (ISTele-T JSs) (DepAtkey (Response (Tele-QT ISs) c) (combine-state tele ∘′ next (Tele-QT ISs))) (combine-state tele (f s))
        lem = combine-tele tele c
        rewrap : ∀{s′}
               → DepAtkey (Response (Tele-QT ISs) c) (combine-state tele ∘′ next (Tele-QT ISs)) s′
               → DepAtkey (Response (Tele-QT ISs) c) ((g &&& combine-state tele ∘′ f) ∘′ nextE emb) (g s , s′)
        rewrap (DepV r) = {!!}
        goal : FreeMonad (ISTele-T JSs) (DepAtkey (Response (Tele-QT ISs) c) ((g &&& combine-state tele ∘′ f) ∘′ nextE emb) ∘′ λ s₂ → g s , s₂) (combine-state tele (f s))
        goal = fmapⁱ rewrap lem
