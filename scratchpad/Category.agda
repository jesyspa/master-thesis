module Category where

open import MiniPrelude

record SmallCategory (Ob : Set) (Hom : Ob → Ob → Set) : Set where
  infixr 10 _∘_
  field
    id : ∀ a → Hom a a
    _∘_ : ∀{a b c} → Hom b c → Hom a b → Hom a c

    id-left-identity : ∀ a b → (f : Hom a b)
                     → f ≡ id b ∘ f
    id-right-identity : ∀ a b → (f : Hom a b)
                      → f ≡ f ∘ id a
    id-comp-assoc : ∀{a b c d} → (f : Hom c d) → (g : Hom b c) → (h : Hom a b)
                  → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

open SmallCategory {{...}} public

instance
  CategoryNat : SmallCategory Nat _≤N_ 
  id {{CategoryNat}} i = refl≤ i
  _∘_ {{CategoryNat}} p q = trans≤ p q
  id-left-identity {{CategoryNat}} a b f = Nat≤-pi f (id b ∘ f)
  id-right-identity {{CategoryNat}} a b f = Nat≤-pi f (f ∘ id a)
  id-comp-assoc {{CategoryNat}} f g h = Nat≤-pi (f ∘ (g ∘ h)) ((f ∘ g) ∘ h)
