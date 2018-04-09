{-# OPTIONS --allow-unsolved-metas #-}
open import Probability.Class using (Probability)
module Distribution.List.BasicProps (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List.Definition Q
open import Distribution.List.SupportProps Q
open import Algebra.Function
open import Algebra.Monoid
open import Algebra.Equality
open import Algebra.SemiringProps Q
open import Probability.Class
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
    sample-invariant-LD : {xs ys : ListDist A} → xs ≡LD ys → (a : A) → sample-LD xs a ≡ sample-LD ys a
    sample-invariant-LD (sample-equiv p) a = p a

    normalize-correct-lemma : (xs : ListDist A) (a : A)
                            → sample-LD xs a ≡ sum (map (sample-LD xs) $ filter (isYes ∘ (_==_ a)) $ support-LD xs)
    normalize-correct-lemma xs a with decide-Index a xs
    ... | yes p =
      sample-LD xs a
        ≡⟨ singleton-sum-id (sample-LD xs a) ⟩
      sum [ sample-LD xs a ]
        ≡⟨ refl ⟩
      sum (map (sample-LD xs) [ a ])
        ≡⟨ (cong (sum ∘ map (sample-LD xs)) $ uniques-gives-singleton (map fst xs)
                                                                      (unique-preserves-elem-inv (map fst xs)
                                                                                                 (support-preserves-elements xs a p))) ⟩
      sum (map (sample-LD xs) $ filter (isYes ∘ (_==_ a)) $ support-LD xs)
      ∎
    ... | no np = cong sum $
      filter-vals a xs
        ≡⟨ not-in-filter-empty a xs np ⟩ʳ
      []
        ≡⟨ cong (map (sample-LD xs)) $ if-not-there-filter-empty a (support-LD xs) (np ∘ support-preserves-elements-inv xs a) ⟩
      map (sample-LD xs) (filter (isYes ∘ (_==_ a)) $ support-LD xs)
      ∎

    normalize-correct-LD : (xs : ListDist A) → xs ≡LD normalize-LD xs
    normalize-correct-LD xs = sample-equiv λ a →
      sum (filter-vals a xs)
        ≡⟨ normalize-correct-lemma xs a ⟩
      sum (map (sample-LD xs) $ filter (isYes ∘ (_==_ a)) $ support-LD xs)
        ≡⟨ cong (sum ∘′ map (sample-LD xs)) $ filter-vals-diag (support-LD xs) a ⟩
      sum (map (sample-LD xs) $ filter-vals a $ map diag (support-LD xs))
        ≡⟨ cong sum $ filter-vals-map (sample-LD xs) (map diag (support-LD xs)) a ⟩
      sum (filter-vals a $ map (second (sample-LD xs)) $ map diag (support-LD xs))
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-comp (second (sample-LD xs)) diag (support-LD xs) ⟩ʳ
      sum (filter-vals a $ map (second (sample-LD xs) ∘′ diag) (support-LD xs))
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-ext (second (sample-LD xs) ∘′ diag)
                                                 (λ x → (x , sample-LD xs x))
                                                 (λ x → refl)
                                                 (support-LD xs) ⟩
      sum (filter-vals a $ map (λ x → (x , sample-LD xs x)) (support-LD xs))
      ∎

  sample-map-mul-writer : ∀{A}{{_ : Eq A}}
                          (xs : ListDist A)(p : Q)(a : A)
                        → p * sample-LD xs a ≡ sample-LD (map (mul-Writer p) xs) a
  sample-map-mul-writer xs p a =
    p * sample-LD xs a
      ≡⟨ mul-sum p (filter-vals a xs)  ⟩
    sum (map (_*_ p) $ filter-vals a xs)
      ≡⟨ (cong sum $ filter-vals-map (_*_ p) xs a) ⟩
    sum (filter-vals a $ map (second (_*_ p)) xs)
    ∎

  bind-universal-prop : ∀{A B}{{_ : Eq B}}
                        (xs : ListDist A)(f : A → ListDist B)(b : B)
                      → sample-LD (xs >>= f) b ≡ sum (map (sample-over-LD f b) xs)
  bind-universal-prop xs f b =
    sum (filter-vals b $ concat $ map (WriterT.bind-MW-helper f) xs)
      ≡⟨ cong sum (filter-vals-concat (map (WriterT.bind-MW-helper f) xs) b ) ⟩
    sum (concat $ map (filter-vals b) $ map (WriterT.bind-MW-helper f) xs)
      ≡⟨ concat-sum-swap (map (filter-vals b) $ map (WriterT.bind-MW-helper f) xs) ⟩
    sum (map sum ∘′ map (filter-vals b) $ map (WriterT.bind-MW-helper f) xs)
      ≡⟨ cong sum $ map-comp sum (filter-vals b) (map (WriterT.bind-MW-helper f) xs) ⟩ʳ
    sum (map (sum ∘′ filter-vals b) $ map (WriterT.bind-MW-helper f) xs)
      ≡⟨ cong sum $ map-comp (sum ∘′ filter-vals b) (WriterT.bind-MW-helper f) xs ⟩ʳ
    sum (map (sum ∘′ filter-vals b ∘′ WriterT.bind-MW-helper f) xs) 
      ≡⟨ cong sum $ map-ext (sum ∘′ filter-vals b ∘′ WriterT.bind-MW-helper f)
                            (sample-over-LD f b)
                            (λ { (a , p) → sym $ sample-map-mul-writer (f a) p b })
                            xs ⟩
    sum (map (sample-over-LD f b) xs)
    ∎

  sbup-helper : ∀{A B}{{_ : Eq B}}
              → (f : A → ListDist B)(b : B)
              → A × Q → Q
  sbup-helper f b (a , q) = q * sample-LD (f a) b

  strong-bind-universal-prop : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
                               (xs : ListDist A)(f : A → ListDist B)(b : B)
                             → sample-LD (xs >>= f) b ≡ sum (map (sbup-helper f b) xs)
  strong-bind-universal-prop xs f b =
    sum (filter-vals b (map (WriterT.bind-MW-helper f) xs))
      ≡⟨ {!!} ⟩
    {!!}
      ≡⟨ {!!} ⟩
    {!!}
      ≡⟨ {!!} ⟩
    sum (map (sbup-helper f b) xs)
    ∎

  sample-over-ext : ∀{A B : Set}{{_ : Eq B}}
                    (f g : A → ListDist B)(b : B)
                    (eq : ∀ a → f a ≡LD g a)
                    (aq : A × Q)
                  → sample-over-LD f b aq ≡ sample-over-LD g b aq
  sample-over-ext f g b eq (a , p) = cong (_*_ p) (sample-invariant-LD (eq a) b)
