open import ThesisPrelude using (Monad)
open import Algebra.Parametrised.Monad 
module Utility.State.TransformerProps {l}(M : Set l → Set l → Set l → Set l){{_ : ParMonad (Set l) M}} where

open import ThesisPrelude
open import Algebra.FunExt
open import Utility.State.Transformer M
import Algebra.Parametrised.MonadProps (Set l) M as PMPM
open import Algebra.Parametrised.MonadProps (Set l) (ParStateT)

module _ {{_ : PMPM.ParMonadProps}} where
  module _ {S S′ : Set l} where
    open import Algebra.FunctorProps (ParStateT S S′)
    import Algebra.FunctorProps (M S S′) as FPM
    open FPM.FunctorProps it
  
    fmap-ext-ST : ∀{A B} (f g : A → B)
                → (∀ a → f a ≡ g a)
                → (st : ParStateT S S′ A)
                → fmap-F f st ≡ fmap-F g st
    fmap-ext-ST f g eq st = fun-ext (λ s → fmap (first f) (st s))
                                    (λ s → fmap (first g) (st s))
                                    (λ s → fmap-ext (first f) (first g) (λ { (a , s′) → cong (λ e → (e , s′)) (eq a) }) (st s))
  
    fmap-id-ST : ∀{A} → (st : ParStateT S S′ A) → st ≡ fmap-F id st
    fmap-id-ST st = fun-ext st (λ s → fmap (first id) (st s)) (λ s → fmap-ext-id (first id) (λ { (a , s′) → refl }) (st s))
  
    fmap-comp-ST : ∀{A B C} (g : B → C) (f : A → B) (st : ParStateT S S′ A) 
                 → fmap-F (g ∘′ f) st ≡ fmap-F g (fmap-F f st)
    fmap-comp-ST g f st = fun-ext (λ s → fmap (first (g ∘′ f)) (st s))
                                  (λ s → fmap (first g) (fmap (first f) (st s)))
                                  ((λ s → fmap-ext (first (g ∘′ f)) (first g ∘′ first f) (λ { (a , s′) → refl }) (st s)
                                      ⟨≡⟩ fmap-comp (first g) (first f) (st s)))
                                      
    instance
      FunctorPropsParStateT : FunctorProps
      FunctorPropsParStateT = record { fmap-ext = fmap-ext-ST ; fmap-id = fmap-id-ST ; fmap-comp = fmap-comp-ST }
  
  open PMPM.ParMonadProps it

  >>=-assocᵖ-ST : ∀{S₀ S₁ S₂ S₃ A B C}
                → (st : ParStateT S₀ S₁ A) → (f : A → ParStateT S₁ S₂ B) → (g : B → ParStateT S₂ S₃ C)
                → (st >>=ᵖ f >>=ᵖ g) ≡ (st >>=ᵖ (λ a → f a >>=ᵖ g))
  >>=-assocᵖ-ST st f g = fun-ext (λ s → (st s >>=ᵖ uncurry f) >>=ᵖ uncurry g)
                                 (λ s → st s >>=ᵖ uncurry (λ a s′ → f a s′ >>=ᵖ uncurry g))
                                 lem
    where
      lem : ∀ s → ((st s >>=ᵖ uncurry f) >>=ᵖ uncurry g) ≡ (st s >>=ᵖ uncurry (λ a s′ → f a s′ >>=ᵖ uncurry g))
      lem s =
        (st s >>=ᵖ uncurry f) >>=ᵖ uncurry g
          ≡⟨ >>=-assocᵖ (st s) (uncurry f) (uncurry g) ⟩
        st s >>=ᵖ (λ a → uncurry f a >>=ᵖ uncurry g)
          ≡⟨ >>=-extᵖ (st s)
                      (λ a → uncurry f a >>=ᵖ uncurry g)
                      (uncurry (λ a s′ → f a s′ >>=ᵖ uncurry g))
                      (λ { (a , s′) → refl}) ⟩
        st s >>=ᵖ uncurry (λ a s′ → f a s′ >>=ᵖ uncurry g)
        ∎

  return->>=-right-idᵖ-ST : ∀{S S′ A} → (st : ParStateT S S′ A) → st ≡ (st >>=ᵖ returnᵖ)
  return->>=-right-idᵖ-ST st = fun-ext st (st >>=ᵖ returnᵖ) λ s →
    st s
      ≡⟨ return->>=-right-idᵖ (st s) ⟩
    st s >>=ᵖ returnᵖ
      ≡⟨ >>=-extᵖ (st s) returnᵖ (uncurry returnᵖ) (λ { (a , s′) → refl }) ⟩
    st s >>=ᵖ uncurry returnᵖ
    ∎

  return->>=-left-idᵖ-ST : ∀{S S′ A B} → (a : A) → (f : A → ParStateT S S′ B)
                         → (returnᵖ a >>=ᵖ f) ≡ f a
  return->>=-left-idᵖ-ST a f = fun-ext (returnᵖ a >>=ᵖ f) (f a) λ s → return->>=-left-idᵖ (a , s) (uncurry f)

  >>=-extᵖ-ST : ∀{S₀ S₁ S₂ A B} (st : ParStateT S₀ S₁ A) (f g : A → ParStateT S₁ S₂ B)
              → (∀ a → f a ≡ g a)
              → (st >>=ᵖ f) ≡ (st >>=ᵖ g)
  >>=-extᵖ-ST st f g eq = fun-ext (st >>=ᵖ f) (st >>=ᵖ g) λ s → >>=-extᵖ (st s) (uncurry f) (uncurry g) λ { (a , s′) → cong (λ e → e s′) (eq a) } 

  instance
    ParMonadPropsParStateT : ParMonadProps
    ParMonadPropsParStateT = record
                               { >>=-assocᵖ = >>=-assocᵖ-ST
                               ; return->>=-right-idᵖ = return->>=-right-idᵖ-ST
                               ; return->>=-left-idᵖ = return->>=-left-idᵖ-ST
                               ; >>=-extᵖ = >>=-extᵖ-ST
                               }
