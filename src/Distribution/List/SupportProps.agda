{-# OPTIONS --allow-unsolved-metas #-}
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
    support-preserves-elements xs a = unique-preserves-elem (map fst xs) ∘′ Index-to-∈ a xs

    support-preserves-elements-inv : (xs : ListDist A) (a : A)
                                   → a ∈ support-LD xs → Index a xs
    support-preserves-elements-inv xs a = ∈-to-Index a xs ∘ unique-preserves-elem-inv (map fst xs) 

    collect-with : (A → Q) → A × Q → Q
    collect-with f (a , q) = q * f a

    data IsSupport : ListDist A → List A → Set where
      EmptySupport : IsSupport [] []
      ConsExistingSupport : (a : A)(q : Q)(xs : ListDist A)(S : List A) → (ix : a ∈ S) → IsSupport xs S → IsSupport ((a , q) ∷ xs) S
      ConsNewSupport : (a : A)(q : Q)(xs : ListDist A)(S : List A) → (nix : ¬(a ∈ S)) → IsSupport xs S → IsSupport ((a , q) ∷ xs) (a ∷ S)

    support-is-support-LD : (xs : ListDist A) → IsSupport xs (support-LD xs)
    support-is-support-LD [] = EmptySupport
    support-is-support-LD ((a , q) ∷ xs) with decide-elem a (map fst xs)
    ... | yes p = ConsExistingSupport a q xs (support-LD xs) (unique-preserves-elem _ p) (support-is-support-LD xs)
    ... | no np = ConsNewSupport a q xs (support-LD xs) (np ∘ unique-preserves-elem-inv _) (support-is-support-LD xs)

    support-of-empty-is-empty : (S : List A)
                              → IsSupport [] S
                              → [] ≡ S
    support-of-empty-is-empty [] EmptySupport = refl
    support-of-empty-is-empty (x ∷ xs) ()

    sample-step : ∀(a : A) q xs → q + sample-LD xs a ≡ sample-LD ((a , q) ∷ xs) a
    sample-step a q xs rewrite yes-refl a = sum-rewrite q (filter-vals a xs)

    sample-missing-irrelevant : ∀(a : A) q xs {S} (p : ¬ (a ∈ S))
                              → (cmb : A × Q → Q)
                              → IsSupport xs S
                              → map (λ x → cmb (x , (sample-LD xs x))) S ≡ map (λ x → cmb (x , (sample-LD ((a , q) ∷ xs) x))) S
    sample-missing-irrelevant a q xs p cmb sup = {!!}

    sample-missing-zero : ∀(a : A) xs {S} (p : ¬ (a ∈ S))
                        → IsSupport xs S
                        → zro ≡ sample-LD xs a
    sample-missing-zero a xs p sup = {!!}

    private
      -- A helper necessary for the next function.
      ssid-cmb : (A → Q) → (A × Q) → Q
      ssid-cmb f (a , q) = q * f a

      ssid-sample-cmb : ListDist A → (A → Q) → A → Q
      ssid-sample-cmb xs f a = ssid-cmb f (a , sample-LD xs a)

    support-sample-invariant-dist : (f : A → Q)(xs : ListDist A){S : List A}
                                    → IsSupport xs S
                                    → sum (map (ssid-cmb f) xs) ≡ sum (map (ssid-sample-cmb xs f) S)
    support-sample-invariant-dist f .[] {[]} EmptySupport = refl
    support-sample-invariant-dist f ._ {[]} (ConsExistingSupport a q xs .[] () sup)
    support-sample-invariant-dist f .((a , q) ∷ xs) {s ∷ S} (ConsExistingSupport a q xs .(s ∷ S) ix sup) =
      sum (q * f a ∷ map (ssid-cmb f) xs)
        ≡⟨ sum-rewrite (q * f a) (map (ssid-cmb f) xs) ⟩ʳ
      q * f a + sum (map (ssid-cmb f) xs)
        ≡⟨ lem ⟩
      sample-LD ((a , q) ∷ xs) s * f s + sum (map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
        ≡⟨ sum-rewrite (sample-LD ((a , q) ∷ xs) s * f s) (map (ssid-sample-cmb ((a , q) ∷ xs) f) S) ⟩
      sum (sample-LD ((a , q) ∷ xs) s * f s ∷ map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
      ∎
      where
        lem : q * f a + sum (map (ssid-cmb f) xs) ≡ sample-LD ((a , q) ∷ xs) s * f s + sum (map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
        lem with s == a
        ... | yes refl =
          q * f s + sum (map (ssid-cmb f) xs)
            ≡⟨ cong (_+_ (q * f a)) {!!} ⟩
          q * f s + (sample-LD xs s * f s + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S))
            ≡⟨ +-assoc (q * f s) (sample-LD xs s * f s) _ ⟩
          (q * f s + sample-LD xs s * f s) + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S)
            ≡⟨ cong (λ e → e + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S)) $ +*-right-dist q (sample-LD xs s) (f s) ⟩ʳ
          (q + sample-LD xs s) * f s + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S)
            ≡⟨ cong (λ e → e * f s + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S)) $ sum-rewrite q (filter-vals s xs) ⟩
          sum (q ∷ filter-vals s xs) * f s + sum (map (ssid-sample-cmb ((s , q) ∷ xs) f) S)
          ∎
        ... | no neq = {!!}
    support-sample-invariant-dist f .((a , q) ∷ xs) {a ∷ S} (ConsNewSupport .a q xs .S nix sup) =
      sum (q * f a ∷ map (ssid-cmb f) xs)
        ≡⟨ sum-rewrite (q * f a) (map (ssid-cmb f) xs) ⟩ʳ
      q * f a + sum (map (ssid-cmb f) xs)
        ≡⟨ cong (λ e → e * f a + sum (map (ssid-cmb f) xs)) (+-unit-right q) ⟩
      (q + zro) * f a + sum (map (ssid-cmb f) xs)
        ≡⟨ cong (λ e → (q + e) * f a + sum (map (ssid-cmb f) xs)) (sample-missing-zero a xs nix sup) ⟩
      (q + sample-LD xs a) * f a + sum (map (ssid-cmb f) xs)
        ≡⟨ cong (λ e → (q + sample-LD xs a) * f a + e) $
             support-sample-invariant-dist f xs sup  ⟩
      (q + sample-LD xs a) * f a + sum (map (ssid-sample-cmb xs f) S)
        ≡⟨ cong (λ e → (q + sample-LD xs a) * f a + sum e) $
             sample-missing-irrelevant a q xs nix (ssid-cmb f) sup ⟩
      (q + sample-LD xs a) * f a + sum (map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
        ≡⟨ cong (λ e → e * f a + sum (map (ssid-sample-cmb ((a , q) ∷ xs) f) S)) $ sample-step a q xs ⟩
      sample-LD ((a , q) ∷ xs) a * f a + sum (map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
        ≡⟨ sum-rewrite (sample-LD ((a , q) ∷ xs) a * f a) (map (ssid-sample-cmb ((a , q) ∷ xs) f) S) ⟩
      sum (sample-LD ((a , q) ∷ xs) a * f a ∷ map (ssid-sample-cmb ((a , q) ∷ xs) f) S)
      ∎

                                    {-
    support-sample-invariant-dist f a q [] (ConsExistingSupport .a .q .[] S ix sup)
      with support-of-empty-is-empty S sup
    support-sample-invariant-dist f a q [] (ConsExistingSupport .a .q .[] .[] () sup) | refl
    support-sample-invariant-dist f a q [] (ConsNewSupport .a .q .[] S nix sup)
      rewrite sym (support-of-empty-is-empty S sup)
            | yes-refl a
            =
      q * f a + force (zro + zro * f a) id
        ≡⟨ (cong (λ e → q * f a + e) $ forceLemma (zro + zro * f a) id) ⟩
      q * f a + (zro + zro * f a)
        ≡⟨ cong (λ e → q * f a + e) (+-unit-left (zro * f a)) ⟩ʳ
      q * f a + (zro * f a)
        ≡⟨ cong (λ e →  q * f a + e) (zro-left-nil (f a)) ⟩ʳ
      q * f a + zro
        ≡⟨ +-unit-right (q * f a) ⟩ʳ
      q * f a
        ≡⟨ cong (λ e → e * f a) (+-unit-left q) ⟩
      (zro + q) * f a
        ≡⟨ +-unit-left ((zro + q) * f a) ⟩
      zro + (zro + q) * f a
        ≡⟨ cong (λ e → zro + e * f a) (forceLemma (zro + q) id) ⟩ʳ
      zro + force (zro + q) id * f a
        ≡⟨ forceLemma (zro + force (zro + q) id * f a) id ⟩ʳ
      force (zro + force (zro + q) id * f a) id
      ∎
    support-sample-invariant-dist f a q ((a′ , q′) ∷ xs) (ConsExistingSupport .a .q .((a′ , q′) ∷ xs) S ix sup) =
      q * f a + sum (map (λ x → sample-LD ((a′ , q′) ∷ xs) x * f x) S)
        ≡⟨ {!!} ⟩
      sum (map (λ x → sample-LD ((a , q) ∷ (a′ , q′) ∷ xs) x * f x) S)
      ∎
    support-sample-invariant-dist f a q ((a′ , q′) ∷ xs) (ConsNewSupport .a .q .((a′ , q′) ∷ xs) S nix sup) =
      q * f a + sum (sample-LD ((a′ , q′) ∷ xs) a * f a ∷ map (λ x → sample-LD ((a′ , q′) ∷ xs) x * f x) S)
        ≡⟨ {!!} ⟩
      sample-LD dist a * f a + sum (map (λ x → sample-LD dist x * f x) S)
        ≡⟨ sum-rewrite (sample-LD dist a * f a)
                       (map (λ x → sample-LD dist x * f x) S) ⟩
      sum (sample-LD dist a * f a ∷ map (λ x → sample-LD dist x * f x) S)
      ∎
      where dist = (a , q) ∷ (a′ , q′) ∷ xs
      -}

    {-
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
                      -}


