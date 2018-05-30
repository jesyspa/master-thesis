module Algebra.Function where

open import ThesisPrelude

Injective : ∀{l l′} {A : Set l} {B : Set l′} → (A → B) → Set (l ⊔ l′)
Injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

comp-Injective : ∀{l l′ l′′} {A : Set l} {B : Set l′} {C : Set l′′}
               → (g : B → C) → (f : A → B)
               → Injective g
               → Injective f
               → Injective (g ∘′ f)
comp-Injective g f pg pf {x} {y} pe = pf (pg {f x} {f y} pe)

id-Injective : ∀{l} {A : Set l}
             → Injective {A = A} id
id-Injective p = p 

Surjective : ∀{l l′} {A : Set l} {B : Set l′} → (A → B) → Set (l ⊔ l′)
Surjective {A = A} {B = B} f = (y : B) → Σ A λ x → y ≡ f x

comp-Surjective : ∀{l l′ l′′} {A : Set l} {B : Set l′} {C : Set l′′}
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
Retraction_of_ : ∀{l l′} {A : Set l} {B : Set l′} (g : B → A) (f : A → B) → Set l
Retraction_of_ {A = A} g f = (a : A) → a ≡ g (f a) 

Section_of_ : ∀{l l′} {A : Set l} {B : Set l′} (g : B → A) (f : A → B) → Set l′
Section g of f = Retraction f of g

Bijective : ∀{l l′} {A : Set l} {B : Set l′} → (A → B) → Set (l ⊔ l′)
Bijective {A = A} {B = B} f = Σ (B → A) λ g → Section f of g × Retraction f of g 

InjSurj-to-Bij : ∀{l l′} {A : Set l} {B : Set l′}
               → (f : A → B)
               → Injective f
               → Surjective f
               → Bijective f
InjSurj-to-Bij f pi ps = fst ∘ ps , (λ a → pi (snd $ ps $ f a)) , snd ∘ ps

Bij-to-Inj : ∀{l l′} {A : Set l} {B : Set l′}
           → (f : A → B)
           → Bijective f
           → Injective f
Bij-to-Inj f (g , pa , pb) {x} {y} = λ p → pa x ⟨≡⟩ cong g p ⟨≡⟩ʳ pa y

Bij-to-Surj : ∀{l l′} {A : Set l} {B : Set l′}
            → (f : A → B)
            → Bijective f
            → Surjective f
Bij-to-Surj f (g , pa , pb) = λ y → g y , pb y


comp-Bijective : ∀{l l′ l′′} {A : Set l} {B : Set l′} {C : Set l′′}
                → (g : B → C) → (f : A → B)
                → Bijective g
                → Bijective f
                → Bijective (g ∘′ f)
comp-Bijective g f (gi , pgia , pgib) (fi , pfia , pfib) = fi ∘′ gi
                                                         , (λ a → pfia a ⟨≡⟩ cong fi (pgia (f a)))
                                                         , λ c → pgib c ⟨≡⟩ cong g (pfib (gi c))

id-Bijective : ∀{l} {A : Set l}
              → Bijective {A = A} id
id-Bijective = (λ x → x) , (λ x → refl) , (λ x → refl)

infix 2 _↔_
_↔_ : ∀{l l′} (A : Set l) (B : Set l′) → Set (l ⊔ l′)
A ↔ B = Σ (A → B) Bijective

get-fun : ∀{l l′} {A : Set l} {B : Set l′}
        → A ↔ B → A → B
get-fun = fst

get-inv : ∀{l l′} {A : Set l} {B : Set l′}
        → A ↔ B → B → A
get-inv = fst ∘ snd

get-Sec : ∀{l l′}{A : Set l}{B : Set l′}
        → (bj : A ↔ B) → Section get-inv bj of get-fun bj
get-Sec (_ , _ , _ , pf) = pf

↔-refl : ∀{l} (A : Set l)
       → A ↔ A
↔-refl A = id , id-Bijective

↔-sym : ∀{l l′} (A : Set l) (B : Set l′)
      → A ↔ B
      → B ↔ A
↔-sym A B (f , g , pfg , pgf) = g , f , pgf , pfg

↔-trans : ∀{l l′ l′′} (A : Set l) (B : Set l′) (C : Set l′′)
        → A ↔ B → B ↔ C
        → A ↔ C
↔-trans A B C (f , pf) (g , pg) = g ∘′ f , comp-Bijective g f pg pf 

