module Interaction.Complete.Elem where

open import ThesisPrelude

data _∈_ {l}{A : Set l} : A → List A → Set where
  here : ∀{xs} a → a ∈ (a ∷ xs)
  there : ∀{a x xs} → a ∈ xs → a ∈ (x ∷ xs)

Elem : ∀{l}{A : Set l} → List A → Set l
Elem xs  = Σ _ (λ a → a ∈ xs)

getElem : ∀{l}{A : Set l} → (xs : List A) → Elem xs → A
getElem xs (a , _) = a

data All {l l′}{A : Set l}(P : A → Set l′) : List A → Set l′ where
  nil : All P []
  cons : ∀{x xs} → P x → All P xs → All P (x ∷ xs)
