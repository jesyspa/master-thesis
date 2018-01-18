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
