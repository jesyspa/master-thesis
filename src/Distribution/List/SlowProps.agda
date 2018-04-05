open import Probability.Class using (Probability)
module Distribution.List.SlowProps (Q : Set) {{PQ : Probability Q}} where
-- AG: These properties take very long to typecheck, so I'm splitting them out.

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

open Probability PQ

module _ {{PPQ : ProbabilityProps}} where
  open ProbabilityProps PPQ
  open SemiringProps srprops
  instance
    private
      MonoidPropsMulQ : MonoidProps Q
      MonoidPropsMulQ = *-is-monoid

  module _ {A} {{_ : Eq A }} where
--   TODO: Acutally reverse the order of statements and update syms.
    irrelevance-LD : ∀ n (xs : ListDist A)
                   → xs ≡LD (uniform-LD n >>= const xs)
    irrelevance-LD n xs = sample-equiv λ a → sym (
      sample-LD (uniform-LD n >>= const xs) a
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

  interchange-LD : ∀{A B C}{{_ : Eq C}}(xs : ListDist A)(ys : ListDist B)
                    (f : A → B → ListDist C)
                  → (xs >>= λ a → ys >>= f a) ≡LD (ys >>= λ b → xs >>= λ a → f a b)
  interchange-LD {A} {B} {C} xs ys f = sample-equiv lem
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
               
