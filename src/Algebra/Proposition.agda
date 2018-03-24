module Algebra.Proposition where

open import ThesisPrelude
open import Algebra.FunExt

IsProposition : Set → Set
IsProposition A = (a₁ a₂ : A) → a₁ ≡ a₂

IsContractible : Set → Set
IsContractible A = Σ A (λ a → ∀ a′ → a ≡ a′) 

void-prop : IsProposition ⊥
void-prop () ()

functions-prop : ∀{A B} → IsProposition B → IsProposition (A → B)
functions-prop p f₁ f₂ = fun-ext f₁ f₂ λ a → p (f₁ a) (f₂ a)

unit-contractible : IsContractible ⊤
unit-contractible = tt , λ { tt → refl }

contractible-is-prop : ∀{A} → IsContractible A → IsProposition A
contractible-is-prop (a , p) a₁ a₂ = p a₁ ʳ⟨≡⟩ p a₂

unit-prop : IsProposition ⊤
unit-prop = contractible-is-prop unit-contractible 

product-contractible : ∀{A B} → IsContractible A → IsContractible B → IsContractible (A × B)
product-contractible (ca , pa) (cb , pb) = (ca , cb) , λ { (ca′ , cb′) → cong₂ _,_ (pa ca′) (pb cb′) }

existential-contractible : ∀{A}(F : A → Set) → IsContractible A → (∀ a → IsContractible (F a)) → IsContractible (Σ A F)
existential-contractible {A} F (ca , pa) p with p ca
... | cf , pf = (ca , cf) , lem
  where lem : (x : Σ A F) → (ca , cf) ≡ x
        lem (ca′ , cf′) rewrite pa ca′ | pf cf′ = refl
