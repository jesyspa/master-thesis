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

    support-unique : ∀{xs S₁ S₂}
                          → IsSupport xs S₁
                          → IsSupport xs S₂
                          → S₁ ≡ S₂
    support-unique EmptySupport EmptySupport = refl
    support-unique (ConsExistingSupport a q xs S₁ ix sup₁) (ConsExistingSupport .a .q .xs S₂ ix₁ sup₂) = support-unique sup₁ sup₂
    support-unique (ConsExistingSupport a q xs S₁ ix sup₁) (ConsNewSupport .a .q .xs S₂ nix sup₂)
      rewrite support-unique sup₁ sup₂ = ⊥-elim (nix ix)
    support-unique (ConsNewSupport a q xs S₁ nix sup₁)     (ConsExistingSupport .a .q .xs S₂ ix sup₂)
      rewrite support-unique sup₁ sup₂ = ⊥-elim (nix ix)
    support-unique (ConsNewSupport a q xs S₁ nix sup₁)     (ConsNewSupport .a .q .xs S₂ nix₁ sup₂)
      = cong (_∷_ a) (support-unique sup₁ sup₂)

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

    support-ix-unique : ∀{xs S a}(_ : IsSupport xs S)
                      → (pt qt : a ∈ S)
                      → pt ≡ qt
    support-ix-unique EmptySupport () ()
    support-ix-unique (ConsExistingSupport a q xs S ix sup) pt qt = support-ix-unique sup pt qt
    support-ix-unique (ConsNewSupport a  q xs S nix sup) (here .a .S)       (here .a .S)        = refl
    support-ix-unique (ConsNewSupport a  q xs S nix sup) (here .a .S)       (there .a .a .S qt) = ⊥-elim (nix qt)
    support-ix-unique (ConsNewSupport .x q xs S nix sup) (there x .x .S pt) (here .x .S)        = ⊥-elim (nix pt)
    support-ix-unique (ConsNewSupport a  q xs S nix sup) (there x .a .S pt) (there .x .a .S qt) = cong there′ (support-ix-unique sup pt qt)

    support-ix-athead : ∀{xs S a}
                      → IsSupport xs (a ∷ S)
                      → ¬(a ∈ S)
    support-ix-athead (ConsExistingSupport a q ys S ix sup) pt = support-ix-athead sup pt
    support-ix-athead (ConsNewSupport a q ys S nix sup)     pt = nix pt

    only-support-sample-nonzero : ∀{xs S a}
                                → IsSupport xs S
                                → ¬ (a ∈ S)
                                → zro ≡ sample-LD xs a
    only-support-sample-nonzero EmptySupport niq = refl
    only-support-sample-nonzero {a = a} (ConsExistingSupport b p xs S ix  sup) niq with a == b
    ... | yes refl  = ⊥-elim $ niq ix
    ... | no  neq   = only-support-sample-nonzero sup niq 
    only-support-sample-nonzero {a = a} (ConsNewSupport      b p xs S nix sup) niq with a == b
    ... | yes refl = ⊥-elim $ niq (here _ _)
    ... | no  neq  = only-support-sample-nonzero sup λ p → niq (there′ p)

    only-support-sample-relevant : ∀{xs S a q}(f : A → Q)
                                 → IsSupport xs S
                                 → ¬ (a ∈ S)
                                 → sum (map (sample-with-LD xs f) S) ≡ sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
    only-support-sample-relevant f EmptySupport nix = refl
    only-support-sample-relevant {.((b , p) ∷ xs)} {.S} {a} {q} f (ConsExistingSupport b p xs S ix sup) nix
      = cong sum (strong-map-ext (sample-with-LD ((b , p) ∷ xs) f)
                                 (sample-with-LD ((a , q) ∷ (b , p) ∷ xs) f)
                                 S lem)
      where
        lem : ∀{a′} → a′ ∈ S → sample-with-LD ((b , p) ∷ xs) f a′ ≡ sample-with-LD ((a , q) ∷ (b , p) ∷ xs) f a′
        lem {a′} pt = {!!}
    only-support-sample-relevant f (ConsNewSupport a q xs S nix₁ sup) nix = {!!}

    only-support-sample-relevant′ : ∀{xs S a q}(f : A → Q)
                                  → IsSupport ((a , q) ∷ xs) (a ∷ S)
                                  → IsSupport xs S
                                  → sum (map (sample-with-LD xs f) S) ≡ sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
    only-support-sample-relevant′ f (ConsExistingSupport a q xs .(a ∷ _) ix sup) sup′
      with support-unique sup sup′
    ... | ()
    only-support-sample-relevant′ f (ConsNewSupport a q xs S nix sup)            sup′
      = cong sum (strong-map-ext (sample-with-LD xs f) (sample-with-LD ((a , q) ∷ xs) f) S lem)
      where
        lem : ∀{b} → b ∈ S → sample-with-LD xs f b ≡ sample-with-LD ((a , q) ∷ xs) f b
        lem {b} pt with b == a
        ... | yes refl = ⊥-elim $ nix pt
        ... | no   neq = refl

    -- This is an essential lemma for showing the strong universal property of bind.
    -- This states that
    --   sum $ map (λ { (a , q) → q * (f a) }) xs
    -- is equal to
    --   sum $ map (λ a → sample xs a * f a) S
    -- where S is the support of xs.  In other words, this is a distributivity lemma.
    support-sample-invariant-dist : (f : A → Q)(xs : ListDist A){S : List A}
                                    → IsSupport xs S
                                    → sum (map (cmb-Writer f) xs) ≡ sum (map (sample-with-LD xs f) S)
    support-sample-invariant-dist f .[] {[]} EmptySupport = refl
    support-sample-invariant-dist f ._ {[]} (ConsExistingSupport a q xs .[] () sup)
    support-sample-invariant-dist f .((a , q) ∷ xs) {s ∷ S} (ConsExistingSupport a q xs .(s ∷ S) ix sup) =
      sum (q * f a ∷ map (cmb-Writer f) xs)
        ≡⟨ sum-rewrite (q * f a) (map (cmb-Writer f) xs) ⟩ʳ
      q * f a + sum (map (cmb-Writer f) xs)
        ≡⟨ cong (λ e → q * f a + e) (support-sample-invariant-dist f xs sup) ⟩
      q * f a + sum (map (sample-with-LD xs f) (s ∷ S))
        ≡⟨ cong (λ e → q * f a + e) (sum-rewrite (sample-with-LD xs f s) (map (sample-with-LD xs f) S)) ⟩ʳ
      q * f a + (sample-LD xs s * f s + sum (map (sample-with-LD xs f) S))
        ≡⟨ lem ⟩
      sample-LD ((a , q) ∷ xs) s * f s + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        ≡⟨ sum-rewrite (sample-LD ((a , q) ∷ xs) s * f s) (map (sample-with-LD ((a , q) ∷ xs) f) S) ⟩
      sum (sample-LD ((a , q) ∷ xs) s * f s ∷ map (sample-with-LD ((a , q) ∷ xs) f) S)
      ∎
      where
        -- IIRC, I concluded that this is simply false in general.
        lem : q * f a + (sample-LD xs s * f s + sum (map (sample-with-LD xs f) S)) ≡ sample-LD ((a , q) ∷ xs) s * f s + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
        lem with s == a
        ... | yes refl =
          q * f s + (sample-LD xs s * f s + sum (map (sample-with-LD xs f) S))
            ≡⟨ +-assoc _ _ _ ⟩
          (q * f s + sample-LD xs s * f s) + sum (map (sample-with-LD xs f) S)
            ≡⟨ cong (λ e → e + sum (map (sample-with-LD xs f) S)) (+*-right-dist _ _ _) ⟩ʳ
          (q + sample-LD xs s) * f s + sum (map (sample-with-LD xs f) S)
            ≡⟨ cong (λ e → (q + sample-LD xs s) * f s + sum e) (strong-map-ext _ _ S lem2) ⟩
          (q + sample-LD xs s) * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)
            ≡⟨ cong (λ e → e * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)) (sum-rewrite q (filter-vals s xs)) ⟩
          sum (q ∷ filter-vals s xs) * f s + sum (map (sample-with-LD ((s , q) ∷ xs) f) S)
          ∎
          where
            lem2 : ∀{t} → t ∈ S → sample-with-LD xs f t ≡ sample-with-LD ((s , q) ∷ xs) f t
            lem2 {t} pt with t == s
            ... | yes refl = ⊥-elim (support-ix-athead sup pt)
            ... | no neq = refl
        ... | no neq =
          q * f a + (sample-LD xs s * f s + sum (map (sample-with-LD xs f) S))
            ≡⟨ +-assoc _ _ _ ⟩
          (q * f a + sample-LD xs s * f s) + sum (map (sample-with-LD xs f) S)
            ≡⟨ cong (λ e → e + sum (map (sample-with-LD xs f) S)) (+-comm _ _) ⟩
          (sample-LD xs s * f s + q * f a) + sum (map (sample-with-LD xs f) S)
            ≡⟨ +-assoc _ _ _ ⟩ʳ
          sample-LD xs s * f s + (q * f a + sum (map (sample-with-LD xs f) S))
            ≡⟨ cong (λ e → sample-LD xs s * f s + e) lem2 ⟩
          sample-LD xs s * f s + sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
          ∎
          where
            lem2 : q * f a + sum (map (sample-with-LD xs f) S) ≡ sum (map (sample-with-LD ((a , q) ∷ xs) f) S)
            lem2 = {!!}
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
