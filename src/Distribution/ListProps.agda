{-# OPTIONS --allow-unsolved-metas #-}
open import Probability.Class using (Probability)
module Distribution.ListProps (Q : Set) {{PQ : Probability Q}} where

open import ThesisPrelude
open import Distribution.Class
open import Distribution.List Q
open import Algebra.Function
open import Algebra.Monoid
open import Algebra.Equality
open import Probability.Class
open import Algebra.SemiringProps Q
open import Probability.PropsClass Q
open import Utility.Num
open import Utility.List.Props
open import Utility.List.Arithmetic Q
open import Utility.List.Elem
open import Utility.List.ElemProps
open import Utility.List.Lookup
open import Utility.List.LookupProps
open import Utility.Writer Q
open import Utility.Vector.BitVec
open import Utility.Product

open Probability PQ

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open SemiringProps srprops
  import Algebra.FunctorComposition List Writer as FComp
  open import Algebra.FunctorProps ListDist
  instance
    private
      MonoidPropsMulQ : MonoidProps Q
      MonoidPropsMulQ = *-is-monoid
  
  import Algebra.ApplicativeComposition List Writer as AComp
  open import Algebra.ApplicativeProps ListDist
  
  import Utility.Writer.Transformer Q List as WriterT
  open import Algebra.MonadProps ListDist
  instance
    MonadPropsListDist : MonadProps
    MonadPropsListDist = WriterT.Props.writer-monad-props-composition
  
  uniform-LD-is-uniform : ∀ n (v : BitVec n)
                        → negpow2 n ≡ sample-LD (uniform-LD n) v
  uniform-LD-is-uniform n v =
    negpow2 n
      ≡⟨ singleton-sum-id (negpow2 n) ⟩
    sum [ negpow2 n ]
      ≡⟨ combine-vals-weak-invariant sum v
                                     (annotate (negpow2 n) (all-bitvecs n))
                                     ([ negpow2 n ])
                                     (all-bitvecs-filter-vals v (negpow2 n)) ⟩
    combine-vals sum v (annotate (negpow2 n) (all-bitvecs n))
    ∎
  
  injections-preserve-filter : ∀{A B} {{_ : Eq A}} {{_ : Eq B}} (f : A → B)
                                  → Injective f
                                  → (D : ListDist A)
                                  → (a : A)
                                  → filter-vals a D ≡ filter-vals (f a) (fmap f D)
  injections-preserve-filter f pf [] a = refl
  injections-preserve-filter f pf ((x , v) ∷ D) a with a == x
  ... | yes refl rewrite yes-refl (f a) = cong (_∷_ v) (injections-preserve-filter f pf D a)
  ... | no neq with f a == f x
  injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | yes eq = ⊥-elim (neq (pf eq))
  injections-preserve-filter f pf ((x , v) ∷ D) a | no neq | no neq′ = injections-preserve-filter f pf D a
  
  injections-preserve-distributions-LD : ∀{A B} {{_ : Eq A}} {{_ : Eq B}} (f : A → B)
                                       → Injective f
                                       → (D : ListDist A)
                                       → (a : A)
                                       → sample-LD D a ≡ sample-LD (fmap f D) (f a)
  injections-preserve-distributions-LD f pf D a = cong sum (injections-preserve-filter f pf D a)
  
  uniform-LD-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                                 → Bijective f 
                                 → uniform-LD n ≡LD fmap f (uniform-LD n)
  uniform-LD-bijection-invariant n f (fi , pa , pb) = sample-equiv λ v →
    sample-LD (uniform-LD n) v
      ≡⟨ uniform-LD-is-uniform n v  ⟩ʳ
    negpow2 n
      ≡⟨ uniform-LD-is-uniform n (fi v) ⟩
    sample-LD (uniform-LD n) (fi v)
      ≡⟨ injections-preserve-distributions-LD f (Bij-to-Inj f (fi , pa , pb)) (uniform-LD n) (fi v) ⟩
    sample-LD (fmap f (uniform-LD n)) (f (fi v))
      ≡⟨ cong (λ e → sample-LD (fmap f (uniform-LD n)) e) (pb v) ⟩ʳ
    sample-LD (fmap f (uniform-LD n)) v
    ∎

  module _ {A} {{_ : Eq A }} where
    support-preserves-elements : (xs : ListDist A) (a : A)
                               → Index a xs → a ∈ support-LD xs
                               -- goal: a ∈ uniques (map fst xs)
    support-preserves-elements xs a = unique-preserves-elem a (map fst xs) ∘′ Index-to-∈ a xs

    support-preserves-elements-inv : (xs : ListDist A) (a : A)
                                   → a ∈ support-LD xs → Index a xs
    support-preserves-elements-inv xs a = ∈-to-Index a xs ∘ unique-preserves-elem-inv a (map fst xs) 

    normalize-correct-lemma : (xs : ListDist A) (a : A)
                            → sample-LD xs a ≡ sum (map (sample-LD xs) $ filter (isYes ∘ (_==_ a)) $ support-LD xs)
    normalize-correct-lemma xs a with decide-Index a xs
    ... | yes p =
      sample-LD xs a
        ≡⟨ singleton-sum-id (sample-LD xs a) ⟩
      sum [ sample-LD xs a ]
        ≡⟨ refl ⟩
      sum (map (sample-LD xs) [ a ])
        ≡⟨ (cong (sum ∘ map (sample-LD xs)) $ uniques-gives-singleton a (map fst xs)
                                                                      (unique-preserves-elem-inv a (map fst xs)
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
      sum (filter-vals a $ map (over-snd (sample-LD xs)) $ map diag (support-LD xs))
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-comp (over-snd (sample-LD xs)) diag (support-LD xs) ⟩ʳ
      sum (filter-vals a $ map (over-snd (sample-LD xs) ∘′ diag) (support-LD xs))
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-ext (over-snd (sample-LD xs) ∘′ diag)
                                                 (λ x → (x , sample-LD xs x))
                                                 (λ x → refl)
                                                 (support-LD xs) ⟩
      sum (filter-vals a $ map (λ x → (x , sample-LD xs x)) (support-LD xs))
      ∎
    
    sample-invariant-LD : {xs ys : ListDist A} → xs ≡LD ys → (a : A) → sample-LD xs a ≡ sample-LD ys a
    sample-invariant-LD (sample-equiv p) a = p a

--   TODO: Acutally reverse the order of statements and update syms.
    irrelevance-LD : ∀ n (xs : ListDist A)
                   → xs ≡LD (uniform-LD n >>F= const xs)
    irrelevance-LD n xs = sample-equiv λ a → sym (
      sample-LD (uniform-LD n >>F= const xs) a
        ≡⟨ refl ⟩
      combine-vals sum a (concatMap (WriterT.bind-MW-helper (const xs)) (uniform-LD n))
        ≡⟨ cong (combine-vals sum a ∘′ concat) $
                map-ext (WriterT.bind-MW-helper (const xs)) (cf ∘′ snd) (λ { (_ , q) → refl }) (uniform-LD n)
                ⟨≡⟩ map-comp cf snd (annotate (negpow2 n) (all-bitvecs n))
                ⟨≡⟩ʳ cong (map cf) (map-snd-annotate-replicate (negpow2 n) (all-bitvecs n)) ⟩
      combine-vals sum a (concat (map cf (replicate (length $ all-bitvecs n) $ negpow2 n)))
        ≡⟨ cong (λ e → combine-vals sum a (concat (map cf (replicate e $ negpow2 n)))) $ all-bitvecs-length n ⟩ʳ
      combine-vals sum a (concat (map cf (replicate (pow2 n) $ negpow2 n)))
        ≡⟨ cong (combine-vals sum a ∘′ concat) (map-replicate (pow2 n) cf $ negpow2 n) ⟩ʳ
      combine-vals sum a (concat (replicate (pow2 n) $ cf $ negpow2 n))
        ≡⟨ combine-sum-concat (replicate (pow2 n) $ cf $ negpow2 n) a  ⟩
      sum (map (combine-vals sum a) (replicate (pow2 n) $ cf $ negpow2 n)) 
        ≡⟨ cong sum (map-replicate (pow2 n) (combine-vals sum a) $ cf $ negpow2 n) ⟩ʳ
      sum (replicate (pow2 n) (combine-vals sum a $ cf $ negpow2 n))
        ≡⟨ sum-replicate (pow2 n) (combine-vals sum a $ cf $ negpow2 n) ⟩ʳ
      embed (pow2 n) * (sum $ filter-vals a $ cf $ negpow2 n)
        ≡⟨ mul-sum (embed $ pow2 n) (filter-vals a $ cf $ negpow2 n)  ⟩
      sum (map (_*_ (embed $ pow2 n)) (filter-vals a $ cf $ negpow2 n))
        ≡⟨ cong sum (filter-vals-map (_*_ (embed $ pow2 n)) (cf $ negpow2 n) a) ⟩
      sum (filter-vals a (map (mul-Writer (embed $ pow2 n)) (cf $ negpow2 n))) 
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-comp (mul-Writer (embed $ pow2 n)) (mul-Writer (negpow2 n)) xs ⟩ʳ
      sum (filter-vals a (map (mul-Writer (embed $ pow2 n) ∘′ mul-Writer (negpow2 n)) xs)) 
        ≡⟨ cong (sum ∘′ filter-vals a) $ map-ext-id (mul-Writer (embed $ pow2 n) ∘′ mul-Writer (negpow2 n))
                                                    (λ x → mul-Writer-id x
                                                       ⟨≡⟩ cong (λ e → mul-Writer e x) (pow2-negpow2-cancel n)
                                                       ⟨≡⟩ mul-Writer-assoc (embed $ pow2 n) (negpow2 n) x )
                                                    xs ⟩ʳ

      sum (filter-vals a xs) 
      ∎)
      where cf : Q → List (A × Q)
            cf q = map (mul-Writer q) xs

  sample-map-mul-writer : ∀{A}{{_ : Eq A}}
                          (xs : ListDist A)(p : Q)(a : A)
                        → p * sample-LD xs a ≡ sample-LD (map (mul-Writer p) xs) a
  sample-map-mul-writer xs p a =
    p * sample-LD xs a
      ≡⟨ mul-sum p (filter-vals a xs)  ⟩
    sum (map (_*_ p) $ filter-vals a xs)
      ≡⟨ (cong sum $ filter-vals-map (_*_ p) xs a) ⟩
    sum (filter-vals a $ map (over-snd (_*_ p)) xs)
    ∎

  bind-universal-prop : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
                        (xs : ListDist A)(f : A → ListDist B)(b : B)
                      → sample-LD (xs >>F= f) b ≡ sum (map (sample-over-LD f b) xs)
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

  sample-over-ext : ∀{A B : Set}{{_ : Eq B}}
                    (f g : A → ListDist B)(b : B)
                    (eq : ∀ a → f a ≡LD g a)
                    (aq : A × Q)
                  → sample-over-LD f b aq ≡ sample-over-LD g b aq
  sample-over-ext f g b eq (a , p) = cong (_*_ p) (sample-invariant-LD (eq a) b)

  >>=-D-ext-LD : ∀{A B} {{_ : Eq A}} {{_ : Eq B}}
               → (xs : ListDist A)
               → (f g : A → ListDist B)
               → (∀ a → f a ≡LD g a)
               → (xs >>F= f) ≡LD (xs >>F= g)
  >>=-D-ext-LD xs f g pf = sample-equiv λ b →
    sample-LD (xs >>F= f) b
      ≡⟨ bind-universal-prop xs f b ⟩
    sum (map (sample-over-LD f b) xs) 
      ≡⟨ (cong sum $ map-ext (sample-over-LD f b) (sample-over-LD g b) (sample-over-ext f g b pf) xs) ⟩
    sum (map (sample-over-LD g b) xs)
      ≡⟨ bind-universal-prop xs g b ⟩ʳ
    sample-LD (xs >>F= g) b
    ∎
               
  open import Distribution.PropsClass ListDist
  
  instance
    DistMonadPropsListDist : DistMonadProps
    DistMonadPropsListDist = record
                               { is-monad = MonadPropsListDist
                               ; is-probability = PPQ
                               ; uniform-is-uniform = uniform-LD-is-uniform
                               ; uniform-bijection-invariant = uniform-LD-bijection-invariant
                               ; sample-equality = sample-equiv
                               ; sample-invariant = sample-invariant-LD
                               ; injection-invariant = injections-preserve-distributions-LD
                               ; irrelevance = irrelevance-LD
                               ; >>=-D-ext = >>=-D-ext-LD
                               }
