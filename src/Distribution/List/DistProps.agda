open import Probability.Class using (Probability)
module Distribution.List.DistProps (Q : Set) {{PQ : Probability Q}} where

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
open import Distribution.List.BasicProps Q
open import Distribution.List.SlowProps Q public

open Probability PQ

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open SemiringProps srprops
  instance
    private
      MonoidPropsMulQ : MonoidProps Q
      MonoidPropsMulQ = *-is-monoid

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

  >>=-D-ext-LD : ∀{A B} {{_ : Eq A}} {{_ : Eq B}}
               → (xs : ListDist A)
               → (f g : A → ListDist B)
               → (∀ a → f a ≡LD g a)
               → (xs >>= f) ≡LD (xs >>= g)
  >>=-D-ext-LD xs f g pf = sample-equiv λ b →
    sample-LD (xs >>= f) b
      ≡⟨ bind-universal-prop xs f b ⟩
    sum (map (sample-over-LD f b) xs) 
      ≡⟨ (cong sum $ map-ext (sample-over-LD f b) (sample-over-LD g b) (sample-over-ext f g b pf) xs) ⟩
    sum (map (sample-over-LD g b) xs)
      ≡⟨ bind-universal-prop xs g b ⟩ʳ
    sample-LD (xs >>= g) b
    ∎

  independence-LD : ∀{A B C}{{_ : Eq C}}(xs : ListDist A)(ys : ListDist B)
                    (f : A → B → ListDist C)
                  → (xs >>= λ a → ys >>= f a) ≡LD (ys >>= λ b → xs >>= λ a → f a b)
  independence-LD {A} {B} {C} xs ys f = sample-equiv lem
    where
      lem : (c : C) → sample-LD (xs >>= λ a → ys >>= f a) c ≡ sample-LD (ys >>= λ b → xs >>= λ a → f a b) c
      lem c =
        sample-LD (xs >>= λ a → ys >>= f a) c 
          ≡⟨ bind-universal-prop xs (λ a → ys >>= f a) c ⟩
        sum (map (sample-over-LD (λ a → ys >>= f a) c) xs)
          ≡⟨ cong sum $ map-ext (sample-over-LD (λ a → ys >>= f a) c)
                                (λ a → sum (map (fun-a a) ys))
                                fun-a-equiv
                                xs ⟩
        sum (map (λ a → sum (map (fun-a a) ys)) xs)
          ≡⟨ cong sum $ map-comp sum (λ a → map (fun-a a) ys) xs ⟩
        sum (map sum $ map (λ a → map (fun-a a) ys) xs)
          ≡⟨ concat-sum-swap (map (λ a → map (fun-a a) ys) xs) ⟩ʳ
        sum (concat $ map (λ a → map (fun-a a) ys) xs)
          ≡⟨ cong (sum ∘′ concat) $ map-comp (flip map ys) fun-a xs ⟩
        sum (concat $ map (flip map ys) (map fun-a xs))
          ≡⟨ flip-sum fun-a xs ys ⟩
        sum (concat $ map (flip map xs) (map (flip fun-a) ys))
          ≡⟨ cong (sum ∘′ concat) $ map-comp (flip map xs) (flip fun-a) ys ⟩ʳ
        sum (concat $ map (λ b → map (flip fun-a b) xs) ys)
          ≡⟨ cong (sum ∘′ concat) $ map-ext (λ b → map (flip fun-a b) xs)
                                            (λ b → map (fun-b b) xs)
                                            (λ b → map-ext (flip fun-a b)
                                                           (fun-b b)
                                                           (fun-equiv b)
                                                           xs)
                                            ys ⟩
        sum (concat $ map (λ b → map (fun-b b) xs) ys)
          ≡⟨ concat-sum-swap (map (λ b → map (fun-b b) xs) ys) ⟩
        sum (map sum $ map (λ b → map (fun-b b) xs) ys)
          ≡⟨ cong sum $ map-comp sum (λ b → map (fun-b b) xs) ys ⟩ʳ
        sum (map (λ b → sum (map (fun-b b) xs)) ys)
          ≡⟨ (cong sum $ map-ext (λ b → sum (map (fun-b b) xs))
                                 (sample-over-LD (λ b → xs >>= λ a → f a b) c)
                                 (sym ∘ fun-b-equiv)
                                 ys) ⟩
        sum (map (sample-over-LD (λ b → xs >>= λ a → f a b) c) ys)
          ≡⟨ bind-universal-prop ys (λ b → xs >>= λ a → f a b) c ⟩ʳ
        sample-LD (ys >>= λ b → xs >>= λ a → f a b) c
        ∎
        where
          fun-gen : (A′ B′ : Set)(f′ : A′ → B′ → ListDist C) → (A′ × Q) → (B′ × Q) → Q
          fun-gen _ _ f′ (a , p) (b , q) = p * q * sample-LD (f′ a b) c
          fun-gen-equiv : (A′ B′ : Set)(f′ : A′ → B′ → ListDist C)(ys′ : ListDist B′)(pa : A′ × Q)
                        → sample-over-LD (λ a → ys′ >>= f′ a) c pa ≡ sum (map (fun-gen A′ B′ f′ pa) ys′)
          fun-gen-equiv A′ B′ f′ ys′ (a , p) =
            p * sum (filter-vals c (concat $ map (WriterT.bind-MW-helper (f′ a)) ys′))
              ≡⟨ cong (λ e → p * sum e) $ filter-vals-concat (map (WriterT.bind-MW-helper (f′ a)) ys′) c ⟩
            p * sum (concat $ map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′))
              ≡⟨ cong (_*_ p) $ concat-sum-swap (map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′)) ⟩
            p * sum (map sum $ map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′))
              ≡⟨ mul-sum p (map sum (map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′))) ⟩
            sum (map (_*_ p) ∘′ map sum $ map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′))
              ≡⟨ cong sum $ map-comp (_*_ p) sum (map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′)) ⟩ʳ
            sum (map (_*_ p ∘′ sum) (map (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′)))
              ≡⟨ cong sum $ map-comp (_*_ p ∘′ sum) (filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′) ⟩ʳ
            sum (map (_*_ p ∘′ sum ∘′ filter-vals c) (map (WriterT.bind-MW-helper (f′ a)) ys′))
              ≡⟨ cong sum $ map-comp (_*_ p ∘′ sum ∘′ filter-vals c) (WriterT.bind-MW-helper (f′ a)) ys′ ⟩ʳ
            sum (map (_*_ p ∘′ sum ∘′ filter-vals c ∘′ WriterT.bind-MW-helper (f′ a)) ys′)
              ≡⟨ cong sum $ map-ext (_*_ p ∘′ sum ∘′ filter-vals c ∘′ WriterT.bind-MW-helper (f′ a))
                                    (fun-gen A′ B′ f′ (a , p))
                                    (λ { (b , q) →
                                      p * sum (filter-vals c (map (second (_*_ q)) (f′ a b)))
                                        ≡⟨ cong (λ e → p * sum e) $ filter-vals-map (_*_ q) (f′ a b) c ⟩ʳ
                                      p * (sum (map (_*_ q) (filter-vals c (f′ a b))))
                                        ≡⟨ cong (_*_ p) $ mul-sum q (filter-vals c (f′ a b))   ⟩ʳ
                                      p * (q * sum (filter-vals c (f′ a b)))
                                        ≡⟨ *-assoc p q (sum (filter-vals c (f′ a b))) ⟩
                                      p * q * sum (filter-vals c (f′ a b))
                                      ∎ })
                                    ys′ ⟩
            sum (map (fun-gen A′ B′ f′ (a , p)) ys′)
            ∎
          fun-a : (A × Q) → (B × Q) → Q
          fun-a = fun-gen A B f
          fun-a-equiv : (pa : A × Q) → sample-over-LD (λ a → ys >>= f a) c pa ≡ sum (map (fun-a pa) ys)
          fun-a-equiv = fun-gen-equiv A B f ys
          fun-b : (B × Q) → (A × Q) → Q
          fun-b = fun-gen B A (flip f)
          fun-b-equiv : (pb : B × Q) → sample-over-LD (λ b → xs >>= flip f b) c pb ≡ sum (map (fun-b pb) xs)
          fun-b-equiv = fun-gen-equiv B A (flip f) xs
          fun-equiv : (pb : B × Q)(pa : A × Q) → flip fun-a pb pa ≡ fun-b pb pa
          fun-equiv (b , q) (a , p) = cong (λ e → e * sample-LD (f a b) c) $ *-comm p q
               
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
                               ; independence = independence-LD
                               ; >>=-D-ext = >>=-D-ext-LD
                               }
