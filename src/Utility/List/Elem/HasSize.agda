import ThesisPrelude as TP
module Utility.List.Elem.HasSize {l}{A : Set l}{{_ : TP.Eq A}} where

open import ThesisPrelude
open import Utility.List.Elem.Definition
open import Algebra.Function
open import Algebra.ExactSize

singleton-size : (a : A) → HasSize (a ∈ [ a ]) 1
singleton-size a = size1-lem (a ∈ [ a ]) (here a []) λ { (here _ .[]) → refl ; (there _ _ .[] ()) }

-- this would probably be a nice lemma to have
-- remove-head : ∀(a : A) (xs : List A) (n : Nat) → HasSize (a ∈ a ∷ xs) (suc n) → HasSize (a ∈ xs) n
-- remove-head a xs n sp = {!!}

remove-head-1 : ∀(a : A) (xs : List A) → HasSize (a ∈ a ∷ xs) 1 → HasSize (a ∈ xs) 0
remove-head-1 a [] s = size0-lem (a ∈ []) (λ ())
remove-head-1 a (x ∷ xs) s = size0-lem (a ∈ x ∷ xs) lem
  where lem : a ∈ x ∷ xs → ⊥
        lem p with is-unique s (here a (x ∷ xs)) (there a a (x ∷ xs) p)
        lem p | ()

reduce-empty-∈ : ∀{x xs} (a : A) → HasSize (a ∈ x ∷ xs) 0 → HasSize (a ∈ xs) 0
reduce-empty-∈ {x} {xs} a s = size0-lem (a ∈ xs) λ p → is-empty s (there a x xs p)

empty-elem : (a : A) (xs : List A) → (HasSize (a ∈ xs) 0) → [] ≡ filter (isYes ∘ (_==_ a)) xs
empty-elem a [] s = refl
empty-elem a (x ∷ xs) s with a == x
... | yes refl = ⊥-elim (is-empty s (here a xs))
... | no neq rewrite sym (empty-elem a xs (reduce-empty-∈ a s)) = refl

singleton-elem : (a : A) (xs : List A) → (HasSize (a ∈ xs) 1) → [ a ] ≡ filter (isYes ∘ (_==_ a)) xs
singleton-elem a [] (f , _) with f zero
singleton-elem a [] (f , _) | ()
singleton-elem a (x ∷ xs) s with a == x
singleton-elem a (.a ∷ xs) s | yes refl = cong (_∷_ a) (empty-elem a xs (remove-head-1 a xs s))
... | no neq = singleton-elem a xs s′
  where v : a ∈ xs 
        v = neq-there a x neq xs (get-unique s) 
        u : (a′ : a ∈ xs) → a′ ≡ v
        u a′ = there-Inj (is-unique s (there a x xs a′) (there a x xs v))
        s′ : HasSize (a ∈ xs) 1
        s′ = size1-lem (a ∈ xs) v u
