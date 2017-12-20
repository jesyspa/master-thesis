module Algebra.Function where

open import ThesisPrelude

Injective : ∀{l} {A B : Set l} → (A → B) → Set l
Injective {A = A} f = (x y : A) → f x ≡ f y → x ≡ y

comp-Injective : ∀{l} {A B C : Set l}
               → (g : B → C) → (f : A → B)
               → Injective g
               → Injective f
               → Injective (g ∘′ f)
comp-Injective g f pg pf x y pe = pf x y (pg (f x) (f y) pe)

id-Injective : ∀{l} {A : Set l}
             → Injective {A = A} id
id-Injective x y p = p 

Surjective : ∀{l} {A B : Set l} → (A → B) → Set l
Surjective {A = A} {B = B} f = (y : B) → Σ A λ x → y ≡ f x

comp-Surjective : ∀{l} {A B C : Set l}
                → (g : B → C) → (f : A → B)
                → Surjective g
                → Surjective f
                → Surjective (g ∘′ f)
comp-Surjective g f pg pf z with pg z
comp-Surjective g f pg pf .(g y) | y , refl with pf y
comp-Surjective g f pg pf .(g (f x)) | .(f x) , refl | x , refl = x , refl


id-Surjective : ∀{l} {A : Set l}
              → Surjective {A = A} id
id-Surjective y = y , refl

-- g is a retraction of f 
Retraction_of_ : ∀{l} {A B : Set l} (g : B → A) (f : A → B) → Set l
Retraction_of_ {A = A} g f = (a : A) → a ≡ g (f a) 

Section_of_ : ∀{l} {A B : Set l} (g : B → A) (f : A → B) → Set l
Section g of f = Retraction f of g

Bijective : ∀{l} {A B : Set l} → (A → B) → Set l
Bijective {A = A} {B = B} f = Σ (B → A) λ g → Section f of g × Retraction f of g 

InjSurj-to-Bij : ∀{l} {A B : Set l}
               → (f : A → B)
               → Injective f
               → Surjective f
               → Bijective f
InjSurj-to-Bij f pi ps = fst ∘ ps , (λ a → pi a (fst $ ps $ f a) (snd $ ps $ f a)) , snd ∘ ps

Bij-to-Inj : ∀{l} {A B : Set l}
           → (f : A → B)
           → Bijective f
           → Injective f
Bij-to-Inj f (g , pa , pb) = λ x y p → pa x ⟨≡⟩ cong g p ⟨≡⟩ʳ pa y

Bij-to-Surj : ∀{l} {A B : Set l}
            → (f : A → B)
            → Bijective f
            → Surjective f
Bij-to-Surj f (g , pa , pb) = λ y → g y , pb y

