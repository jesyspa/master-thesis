{-# OPTIONS --allow-unsolved-metas #-}
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
open DistMonad DistMonadListDist

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

  >>=-D-ext-LD : ∀{A B}{{_ : Eq B}}
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

  >>=-D-approx-ext-LD : ∀{A B}{{_ : Eq B}}
                      → (DA : ListDist A)
                      → (Df Dg : A → ListDist B)
                      → (ε : Q)
                      → (∀ a → bounded-dist-diff (Df a) (Dg a) ε)
                      → bounded-dist-diff (DA >>= Df) (DA >>= Dg) ε
  >>=-D-approx-ext-LD DA Df Dg ε pf a = {!!}

  return-sample-1-LD : ∀{A}{{_ : Eq A}}(a : A) → one ≡ sample-LD (return a) a
  return-sample-1-LD a rewrite yes-refl a = singleton-sum-id one

  return-sample-0-LD : ∀{A}{{_ : Eq A}}(a a′ : A) → ¬ (a ≡ a′) → zro ≡ sample-LD (return a) a′
  return-sample-0-LD a a′ np rewrite no-neq a′ a (np ∘′ sym) = refl

  >>=-D-inv-normal2-LD : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
                       → (xs ys : ListDist A)
                       → (f : A → ListDist B)
                       → xs ≡LD ys
                       → (normalize-LD xs >>= f) ≡LD (normalize-LD ys >>= f)
  >>=-D-inv-normal2-LD xs ys f eq = sample-equiv λ b →
    {!!}
      ≡⟨ {!!} ⟩
    {!!}
    ∎

  >>=-D-inv-normal-LD : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
                      → (xs : ListDist A)
                      → (f : A → ListDist B)
                      → (xs >>= f) ≡LD (normalize-LD xs >>= f)
  >>=-D-inv-normal-LD xs f = sample-equiv λ b →
    sum (filter-vals b (xs >>= f))
      ≡⟨ {!!} ⟩
    sum (filter-vals b (normalize-LD xs >>= f))
    ∎

  >>=-D-inv-LD : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
               → (xs ys : ListDist A)
               → (f : A → ListDist B)
               → xs ≡LD ys
               → (xs >>= f) ≡LD (ys >>= f) 
  >>=-D-inv-LD xs ys f eq = sample-equiv λ b →
    sample-LD (xs >>= f) b
      ≡⟨ sample-invariant-LD (>>=-D-inv-normal-LD xs f) b ⟩
    sample-LD (normalize-LD xs >>= f) b
      ≡⟨ sample-invariant-LD (>>=-D-inv-normal2-LD xs ys f eq) b ⟩
    sample-LD (normalize-LD ys >>= f) b
      ≡⟨ sample-invariant-LD (>>=-D-inv-normal-LD ys f) b ⟩ʳ
    sample-LD (ys >>= f) b
    ∎

  return-certain-LD : ∀{A}{{_ : Eq A}}(a : A) → sample-LD (return a) a ≡ one
  return-certain-LD a rewrite yes-refl a = sym (singleton-sum-id one)

  uniform-not-return-LD : ∀ n (v : BitVec n) → ¬(n ≡ 0) → ¬(uniform-LD n ≡LD return v)
  uniform-not-return-LD n v ne p with embed-Inj {suc zero} {pow2 n} (embed-1 ʳ⟨≡⟩ lem2)
    where
      lem : negpow2 n ≡ one
      lem =
        negpow2 n
          ≡⟨ uniform-LD-is-uniform n v ⟩
        sample-LD (uniform-LD n) v
          ≡⟨ sample-invariant-LD p v ⟩
        sample-LD (return v) v
          ≡⟨ return-certain-LD v ⟩
        one
        ∎
      lem2 : one ≡ embed (pow2 n)
      lem2 =
        one
          ≡⟨ pow2-negpow2-cancel n ⟩
        embed (pow2 n) * negpow2 n
          ≡⟨ cong (_*_ (embed (pow2 n))) lem ⟩
        embed (pow2 n) * one
          ≡⟨ *-unit-right (embed (pow2 n)) ⟩ʳ
        embed (pow2 n)
        ∎
  ... | z = ne lem3
    where
      lem3 : n ≡ 0
      lem3 = {!!}
               
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
                               ; return-certain = return-certain-LD
                               ; injection-invariant = injections-preserve-distributions-LD
                               ; irrelevance = irrelevance-LD
                               ; interchange = interchange-LD
                               ; >>=-D-ext = >>=-D-ext-LD
                               ; >>=-D-approx-ext = >>=-D-approx-ext-LD
                               ; return-sample-1 = return-sample-1-LD
                               ; return-sample-0 = return-sample-0-LD
                               ; >>=-D-inv = >>=-D-inv-LD
                               ; uniform-not-return = uniform-not-return-LD
                               }

