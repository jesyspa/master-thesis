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
    sample-missing-irrelevant a q xs {S} p cmb sup = strong-map-ext (λ x → cmb (x , (sample-LD xs x)))
                                                                    (λ x → cmb (x , (sample-LD ((a , q) ∷ xs) x)))
                                                                    S
                                                                    (λ {x} pt → cong (λ e → cmb (x , e)) (lem pt))
      where
        lem : ∀{x} → x ∈ S → sample-LD xs x ≡ sample-LD ((a , q) ∷ xs) x 
        lem {x} pt with x == a
        ... | yes refl = ⊥-elim (p pt)
        ... | no neq = refl

    sample-missing-zero : ∀(a : A) xs {S} (p : ¬ (a ∈ S))
                        → IsSupport xs S
                        → zro ≡ sample-LD xs a
    sample-missing-zero a .[] p EmptySupport = refl
    sample-missing-zero a .((a′ , q) ∷ xs) p (ConsExistingSupport a′ q xs S ix sup) with a == a′
    ... | yes refl = ⊥-elim (p ix)
    ... | no neq = sample-missing-zero a xs p sup
    sample-missing-zero a .((a′ , q) ∷ xs) p (ConsNewSupport a′ q xs S nix sup) with a == a′
    ... | yes refl = ⊥-elim (p (here a′ S))
    ... | no neq = sample-missing-zero a xs (λ pt → p (there′ pt)) sup 

    support-sample-invariant-dist : (f : A → Q)(xs : ListDist A){S : List A}
                                    → IsSupport xs S
                                    → sum (map (cmb-Writer f) xs) ≡ sum (map (sample-with-LD xs f) S)
    support-sample-invariant-dist f .[] {[]} EmptySupport = refl
    support-sample-invariant-dist f ._ {[]} (ConsExistingSupport a q xs .[] () sup)
    support-sample-invariant-dist f .((a , q) ∷ xs) {s ∷ S} (ConsExistingSupport a q xs .(s ∷ S) ix sup) =
      sum (q * f a ∷ map (cmb-Writer f) xs)
        ≡⟨ sum-rewrite (q * f a) (map (cmb-Writer f) xs) ⟩ʳ
      q * f a + sum (map (cmb-Writer f) xs)
        ≡⟨ lem ⟩
      sample-LD ((a , q) ∷ xs) s * f s + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        ≡⟨ sum-rewrite (sample-LD ((a , q) ∷ xs) s * f s) (map (sample-with-LD ((a , q) ∷ xs) f) S) ⟩
      sum (sample-LD ((a , q) ∷ xs) s * f s ∷ map (sample-with-LD ((a , q) ∷ xs) f) S)
      ∎
      where
        -- IIRC, I concluded that this is simply false in general.
        lem : q * f a + sum (map (cmb-Writer f) xs) ≡ sample-LD ((a , q) ∷ xs) s * f s + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        lem with s == a
        ... | yes refl =
          q * f s + sum (map (cmb-Writer f) xs)
            ≡⟨ cong (_+_ (q * f a)) {!!} ⟩
          q * f s + (sample-LD xs s * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S))
            ≡⟨ +-assoc (q * f s) (sample-LD xs s * f s) _ ⟩
          (q * f s + sample-LD xs s * f s) + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)
            ≡⟨ cong (λ e → e + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)) $ +*-right-dist q (sample-LD xs s) (f s) ⟩ʳ
          (q + sample-LD xs s) * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)
            ≡⟨ cong (λ e → e * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)) $ sum-rewrite q (filter-vals s xs) ⟩
          sum (q ∷ filter-vals s xs) * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)
          ∎
        ... | no neq = {!!}
    support-sample-invariant-dist f .((a , q) ∷ xs) {a ∷ S} (ConsNewSupport .a q xs .S nix sup) =
      sum (q * f a ∷ map (cmb-Writer f) xs)
        ≡⟨ sum-rewrite (q * f a) (map (cmb-Writer f) xs) ⟩ʳ
      q * f a + sum (map (cmb-Writer f) xs)
        ≡⟨ cong (λ e → e * f a + sum (map (cmb-Writer f) xs)) (+-unit-right q) ⟩
      (q + zro) * f a + sum (map (cmb-Writer f) xs)
        ≡⟨ cong (λ e → (q + e) * f a + sum (map (cmb-Writer f) xs)) (sample-missing-zero a xs nix sup) ⟩
      (q + sample-LD xs a) * f a + sum (map (cmb-Writer f) xs)
        ≡⟨ cong (λ e → (q + sample-LD xs a) * f a + e) $
             support-sample-invariant-dist f xs sup  ⟩
      (q + sample-LD xs a) * f a + sum (map (sample-with-LD xs f) S)
        ≡⟨ cong (λ e → (q + sample-LD xs a) * f a + sum e) $
             sample-missing-irrelevant a q xs nix (cmb-Writer f) sup ⟩
      (q + sample-LD xs a) * f a + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        ≡⟨ cong (λ e → e * f a + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)) $ sample-step a q xs ⟩
      sample-LD ((a , q) ∷ xs) a * f a + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        ≡⟨ sum-rewrite (sample-LD ((a , q) ∷ xs) a * f a) (map (sample-with-LD ((a , q) ∷ xs) f) S) ⟩
      sum (sample-LD ((a , q) ∷ xs) a * f a ∷ map (sample-with-LD ((a , q) ∷ xs) f) S)
      ∎

    support-gives-normalize-LD : (f : A → Q)(xs : ListDist A)
                               → sum (map (cmb-Writer f) xs) ≡ sum (map (cmb-Writer f) (normalize-LD xs))
    support-gives-normalize-LD f xs =
      sum (map (cmb-Writer f) xs)
        ≡⟨ support-sample-invariant-dist f xs (support-is-support-LD xs) ⟩
      sum (map (sample-with-LD xs f) (support-LD xs))
        ≡⟨ cong sum (map-comp (cmb-Writer f) (λ x → (x , sample-LD xs x)) (support-LD xs)) ⟩
      sum (map (cmb-Writer f) (map (λ x → (x , sample-LD xs x)) (support-LD xs)))
      ∎


    support-normalize-invariant-LD : (xs : ListDist A) → support-LD xs ≡ support-LD (normalize-LD xs)
    support-normalize-invariant-LD xs =
      uniques (map fst xs)
        ≡⟨ uniques-idempotent (map fst xs) ⟩
      uniques (uniques (map fst xs))
        ≡⟨ cong uniques (map-ext-id (fst ∘′ (λ x → (x , sample-LD xs x))) (λ a → refl) (uniques (map fst xs))) ⟩
      uniques (map (fst ∘′ (λ x → (x , sample-LD xs x))) (uniques (map fst xs)))
        ≡⟨ cong uniques (map-comp fst (λ x → (x , sample-LD xs x)) (uniques (map fst xs))) ⟩
      uniques (map fst (map (λ x → (x , sample-LD xs x)) (uniques (map fst xs))))
      ∎
