module Algebra.Function where

open import ThesisPrelude

Injective : ∀{l} (A B : Set l) → (A → B) → Set l
Injective A B f = (x y : A) → f x ≡ f y → x ≡ y

comp-Injective : ∀{l} {A B C : Set l}
               → (g : B → C) → (f : A → B)
               → Injective B C g
               → Injective A B f
               → Injective A C (g ∘′ f)
comp-Injective g f pg pf x y pe = pf x y (pg (f x) (f y) pe)

id-Injective : ∀{l} {A : Set l}
             → Injective A A id
id-Injective x y p = p 

Surjective : ∀{l} (A B : Set l) → (A → B) → Set l
Surjective A B f = (y : B) → Σ A λ x → y ≡ f x

comp-Surjective : ∀{l} {A B C : Set l}
                → (g : B → C) → (f : A → B)
                → Surjective B C g
                → Surjective A B f
                → Surjective A C (g ∘′ f)
comp-Surjective g f pg pf z with pg z
comp-Surjective g f pg pf .(g y) | y , refl with pf y
comp-Surjective g f pg pf .(g (f x)) | .(f x) , refl | x , refl = x , refl


id-Surjective : ∀{l} {A : Set l}
              → Surjective A A id
id-Surjective y = y , refl

Bijective : ∀{l} (A B : Set l) → (A → B) → Set l
Bijective A B f = Σ (B → A) λ g → ((a : A) → a ≡ g (f a)) × ((b : B) → b ≡ f (g b))

InjSurj-to-Bij : ∀{l} (A B : Set l)
               → (f : A → B)
               → Injective A B f
               → Surjective A B f
               → Bijective A B f
InjSurj-to-Bij A B f pi ps = fst ∘ ps , (λ a → pi a (fst $ ps $ f a) (snd $ ps $ f a)) , snd ∘ ps

Bij-to-Inj : ∀{l} (A B : Set l)
           → (f : A → B)
           → Bijective A B f
           → Injective A B f
Bij-to-Inj A B f (g , pa , pb) = λ x y p → pa x ⟨≡⟩ cong g p ⟨≡⟩ʳ pa y

Bij-to-Surj : ∀{l} (A B : Set l)
            → (f : A → B)
            → Bijective A B f
            → Surjective A B f
Bij-to-Surj A B f (g , pa , pb) = λ y → g y , pb y

