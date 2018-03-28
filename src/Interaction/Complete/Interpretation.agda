open import ThesisPrelude
module Interaction.Complete.Interpretation (M : Set → Set){{_ : Monad M}} where

open import Algebra.Proposition
open import Interaction.Complete.InteractionStructure 
open import Interaction.Complete.FreeMonad 
open import Interaction.Complete.Player 
open import Interaction.Complete.Combine 

open InteractionStructure
open ISMorphism
open MethodSig
open PlayerSig
open PlayerDef

Interpretation : (IS : InteractionStructure) → Set
Interpretation IS = (c : Command IS) → M (Response IS c)

Interpretation-is-FunctorMorphism : ∀{IS} → Interpretation IS → FunctorMorphism (FreeMonad IS) M
Interpretation-is-FunctorMorphism interp (Return-FM a) = return a
Interpretation-is-FunctorMorphism interp (Invoke-FM c cont) = interp c >>= λ r → Interpretation-is-FunctorMorphism interp (cont r)

fmap-Interp : {IS₁ IS₂ : InteractionStructure}(m : ISMorphism IS₁ IS₂)
            → Interpretation IS₂
            → Interpretation IS₁
fmap-Interp m interp c = fmap (ResponseF m) (interp (CommandF m c))

Interpret-PD : (def : PlayerDef)(int : Interpretation (IS-PD def)) → Impl-PD def → PlayerImpl M (Sig-PD def)
Interpret-PD def int = Reinterpret-PI (FreeMonad (IS-PD def)) M (Interpretation-is-FunctorMorphism int)
