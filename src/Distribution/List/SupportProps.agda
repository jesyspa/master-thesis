open import Probability.Class using (Probability)
module Distribution.List.SupportProps (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List.Definition Q
open import Algebra.Function
open import Algebra.Monoid
open import Algebra.Equality
open import Probability.Class
open import Algebra.SemiringProps Q
open import Probability.PropsClass Q
open import Utility.Num
open import Utility.List
open import Utility.List.Arithmetic Q
open import Utility.Writer Q
open import Utility.Vector.BitVec
open import Utility.Product
open import Distribution.List.MonadProps Q
import Utility.Writer.Transformer Q List as WriterT

open Probability PQ

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open SemiringProps srprops
  instance
    private
      MonoidPropsMulQ : MonoidProps Q
      MonoidPropsMulQ = *-is-monoid

  module _ {A} {{_ : Eq A}} where
    support-preserves-elements : (xs : ListDist A) (a : A)
                               → Index a xs → a ∈ support-LD xs
                               -- goal: a ∈ uniques (map fst xs)
    support-preserves-elements xs a = unique-preserves-elem a (map fst xs) ∘′ Index-to-∈ a xs

    support-preserves-elements-inv : (xs : ListDist A) (a : A)
                                   → a ∈ support-LD xs → Index a xs
    support-preserves-elements-inv xs a = ∈-to-Index a xs ∘ unique-preserves-elem-inv a (map fst xs) 

    collect-with : (A → Q) → A × Q → Q
    collect-with f (a , q) = q * f a

    data IsSupport : ListDist A → List A → Set where
      EmptySupport : IsSupport [] []
      ConsExistingSupport : (a : A)(q : Q)(xs : ListDist A)(S : List A) → (a ∈ S) → IsSupport xs S → IsSupport ((a , q) ∷ xs) S
      ConsNewSupport : (a : A)(q : Q)(xs : ListDist A)(S : List A) → ¬(a ∈ S) → IsSupport xs S → IsSupport ((a , q) ∷ xs) (a ∷ S)
      -- AG: It's really annoying to have this, but it can't be derived from the other three.
      PermuteSupport : (a : A)(xs : ListDist A)(S : List A) → (a ∈ S) → IsSupport xs S → IsSupport xs (a ∷ filter-is-not a S)

    support-is-support-LD : (xs : ListDist A) → IsSupport xs (support-LD xs)
    support-is-support-LD [] = EmptySupport
    support-is-support-LD ((a , q) ∷ xs) with decide-elem a (support-LD xs)
    ... | yes p = PermuteSupport a ((a , q) ∷ xs) (support-LD xs) p (ConsExistingSupport a q xs (support-LD xs) p (support-is-support-LD xs))
    ... | no np rewrite sym (if-not-there-filter-equal a (support-LD xs) np)
                      = ConsNewSupport a q xs (support-LD xs) np (support-is-support-LD xs)

    support-sample-invariant-lem : (f : A → Q)(xs : ListDist A){S : List A}
                                 → IsSupport xs S
                                 → sum (map (collect-with f) xs) ≡ sum (map (λ x → sample-LD xs x * f x) S)
    support-sample-invariant-lem f ._ EmptySupport = refl
    support-sample-invariant-lem f ._ (ConsExistingSupport a q xs S np sup) = {!!}
    support-sample-invariant-lem f ._ (ConsNewSupport a q xs S np sup) = {!!}
    support-sample-invariant-lem f xs (PermuteSupport a .xs S np sup) = {!!}

    support-sample-invariant-LD : (f : A → Q)(xs : ListDist A)
                                → sum (map (collect-with f) xs) ≡ sum (map (λ x → sample-LD xs x * f x) (support-LD xs))
    support-sample-invariant-LD f xs = {!!}


