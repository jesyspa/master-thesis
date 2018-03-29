module Interaction.Complete.Elem where

open import ThesisPrelude

data Elem {l}{A : Set l} : List A → Set where
  this : ∀{xs} a → Elem (a ∷ xs)
  that : ∀{x xs} → Elem xs → Elem (x ∷ xs)

getElem : ∀{l}{A : Set l}{xs : List A} → Elem xs → A
getElem (this a) = a
getElem (that p) = getElem p

data All {l l′}{A : Set l}(P : A → Set l′) : List A → Set l′ where
  nil : All P []
  cons : ∀{x xs} → P x → All P xs → All P (x ∷ xs)
