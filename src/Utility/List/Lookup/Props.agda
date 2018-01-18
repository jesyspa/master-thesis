module Utility.List.Lookup.Props {l}{A : Set l} where

open import ThesisPrelude
open import Algebra.Function
open import Utility.Product
open import Utility.List.Props
open import Utility.List.Lookup.Definition

module _ {B : Set l} where
  map-fst-annotate-Ret : (b : B) → Retraction map fst of annotate {A = A} b
  map-fst-annotate-Ret b xs = map-ext-id (fst ∘′ rev-pair b) (λ a → refl) xs ⟨≡⟩ map-comp fst (rev-pair b) xs

  map-snd-annotate-const : (b : B) → (xs : List A) → map (const b) xs ≡ map snd (annotate b xs)
  map-snd-annotate-const b [] = refl
  map-snd-annotate-const b (x ∷ xs) rewrite sym (map-snd-annotate-const b xs) = refl

  map-snd-annotate-replicate : (b : B) → (xs : List A) → replicate (length xs) b ≡ map snd (annotate b xs)
  map-snd-annotate-replicate b xs = map-const b xs ⟨≡⟩ map-snd-annotate-const b xs
