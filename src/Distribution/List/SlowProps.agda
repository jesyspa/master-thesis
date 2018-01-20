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
