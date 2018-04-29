open import Distribution.Class using (DistMonad)
module Distribution.PropsClass (F : Set → Set) {{DF : DistMonad F}} where

open DistMonad DF
open import ThesisPrelude
open import Probability.Class
open import Algebra.MonadProps F
open import Algebra.ApplicativeProps F
open import Algebra.FunctorProps F
open import Algebra.FiniteSet
open import Utility.Vector
open import Utility.List
open import Utility.List.Arithmetic probability
open import Algebra.Function
open import Algebra.LiftingProps F
open import Algebra.LiftingProps (λ τ → Vec {lzero} τ 1) as V1LProps
open import Probability.PropsClass probability
open import Algebra.SubtractiveProps probability
open import Algebra.Preorder probability
open import Algebra.SemiringProps probability

record DistMonadProps : Set₂ where
  field
    overlap {{is-monad}} : MonadProps
    overlap {{is-probability}} : ProbabilityProps
  open MonadProps is-monad
  open ApplicativeProps aprops
  open FunctorProps fprops
  open Probability probability-super
  open ProbabilityProps is-probability
  open SemiringProps srprops
  open SubtractiveProps subprops
  open PreorderProps poprops
  field
    uniform-is-uniform : ∀ n (xs : BitVec n) → negpow2 n ≡ sample (uniform n) xs
    uniform-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                                → Bijective f
                                → uniform n ≡D fmap-F f (uniform n)
    injection-invariant : ∀{A B} {{_ : Eq A}} {{_ : Eq B}}
                        → (f : A → B)
                        → Injective f
                        → (D : F A)
                        → (a : A)
                        → sample D a ≡ sample (fmap f D) (f a)
    irrelevance : ∀{A} {{_ : Eq A}} n (D : F A)
                → D ≡D (uniform n >>= const D)
    interchange : ∀{A B C}{{_ : Eq C}}(DA : F A)(DB : F B)
                   (f : A → B → F C)
                → (DA >>= λ a → DB >>= f a) ≡D (DB >>= λ b → DA >>= λ a → f a b)
    return-sample-1 : ∀{A}{{_ : Eq A}}(a : A) → one ≡ sample (return a) a
    return-sample-0 : ∀{A}{{_ : Eq A}}(a a′ : A) → ¬ (a ≡ a′) → zro ≡ sample (return a) a′


    >>=-D-ext : ∀{A B}{{_ : Eq B}}
              → (Da : F A)
              → (Df Dg : A → F B)
              → (∀ a → Df a ≡D Dg a)
              → (Da >>= Df) ≡D (Da >>= Dg) 
  
    >>=-D-inv : ∀{A B}{{_ : Eq A}}{{_ : Eq B}}
              → (Da Db : F A)
              → (Df : A → F B)
              → (Da ≡D Db)
              → (Da >>= Df) ≡D (Db >>= Df) 

    >>=-D-approx-ext : ∀{A B}{{_ : FiniteSet A}}{{_ : FiniteSet B}}
                     → (DA : F A)
                     → (Df Dg : A → F B)
                     → (ε : probability)
                     → (∀ a → bounded-dist-diff (Df a) (Dg a) ε)
                     → bounded-dist-diff (DA >>= Df) (DA >>= Dg) ε

    >>=-D-approx-inv : ∀{A B}{{_ : FiniteSet A}}{{_ : FiniteSet B}}
                     → (Da Db : F A)
                     → (Df : A → F B)
                     → (ε : probability)
                     → bounded-dist-diff Da Db ε
                     → bounded-dist-diff (Da >>= Df) (Db >>= Df) ε
    uniform-not-return : ∀ n v → ¬(0 ≡ n) → ¬(uniform n ≡D return v)

  sample-invariant-≤zro : ∀{A}{{_ : Eq A}}{D₁ D₂ : F A} → (a : A) → D₁ ≡D D₂ → sample-diff D₁ D₂ a ≤ zro
  sample-invariant-≤zro {D₂ = D₂} a eq rewrite sample-invariant eq a
                                             | sub-cancelling (sample D₂ a)
                                             | sym (abs-pos (≤-refl _)) = ≤-refl _

  bounded-dist-bounds-elements : ∀{A}{{_ : FiniteSet A}}
                               → (D₁ D₂ : F A)
                               → (ε : probability)
                               → bounded-dist-diff D₁ D₂ ε
                               → (a : A)
                               → bounded-diff (sample D₁ a) (sample D₂ a) ε
  bounded-dist-bounds-elements {A} D₁ D₂ ε pf a = ≤-trans lem pf
    where
      lem = sum-bounds-individuals (map-preserves-in (sample-diff D₁ D₂) a (finite-set-list A) (finite-set-list-complete A a))
                                   (map-preserves-prop (sample-diff D₁ D₂) (_≤_ zro) (λ a → abs-nonneg _) (finite-set-list A))

  bounded-dist-0-eq : ∀{A}{{_ : FiniteSet A}}
                    → (D₁ D₂ : F A)
                    → bounded-dist-diff D₁ D₂ zro
                    → D₁ ≡D D₂
  bounded-dist-0-eq D₁ D₂ pf = sample-equiv λ a → abs-zero-eq (abs-zero-min (bounded-dist-bounds-elements D₁ D₂ zro pf a))

  dist-0-eq-elem-inv : ∀{A}{{_ : Eq A}}
                     → (D₁ D₂ : F A)
                     → D₁ ≡D D₂
                     → (a : A)
                     → zro ≡ sample-diff D₁ D₂ a
  dist-0-eq-elem-inv D₁ D₂ eq a
    rewrite sample-invariant eq a
          | sub-cancelling (sample D₂ a) = abs-pos (≤-refl _)

  dist-0-eq-inv : ∀{A}{{_ : FiniteSet A}}
                → (D₁ D₂ : F A)
                → D₁ ≡D D₂
                → zro ≡ dist-diff D₁ D₂
  dist-0-eq-inv {A} D₁ D₂ pf =
    zro
      ≡⟨ zro-left-nil (embed (length (finite-set-list A))) ⟩
    zro * embed (length (finite-set-list A))
      ≡⟨ sum-const-mul zro (finite-set-list A)⟩ʳ
    sum (map (const zro) (finite-set-list A))
      ≡⟨ cong sum $ map-ext (const zro) (sample-diff D₁ D₂) (dist-0-eq-elem-inv D₁ D₂ pf) (finite-set-list A) ⟩
    sum (map (sample-diff D₁ D₂) (finite-set-list A))
    ∎

  bounded-dist-0-eq-inv : ∀{A}{{_ : FiniteSet A}}
                        → (D₁ D₂ : F A)
                        → D₁ ≡D D₂
                        → bounded-dist-diff D₁ D₂ zro
  bounded-dist-0-eq-inv D₁ D₂ pf rewrite sym (dist-0-eq-inv D₁ D₂ pf) = ≤-refl _

  coin-bijection-invariant : (f : Bool → Bool)
                           → Bijective f
                           → coin ≡D fmap-F f coin
  coin-bijection-invariant f pf = sample-equiv λ a →
    sample coin a
      ≡⟨ injection-invariant head head1-Inj (uniform 1) (a ∷ []) ⟩ʳ
    sample (uniform 1) (a ∷ [])
      ≡⟨ sample-invariant (uniform-bijection-invariant 1 (fmap f) (V1LProps.fmap-lift-Bij f pf)) (a ∷ [])  ⟩
    sample (fmap-F (fmap f) (uniform 1)) (a ∷ [])
      ≡⟨ injection-invariant head head1-Inj (fmap-F (fmap f) (uniform 1)) (a ∷ []) ⟩
    sample (fmap-F head (fmap-F (fmap f) (uniform 1))) a
      ≡⟨ cong (λ e → sample e a) (fmap-comp head (fmap f) (uniform 1)
                                 ʳ⟨≡⟩ fmap-ext  (f ∘ head) (head ∘ fmap f) (head-nattrans f) (uniform 1)
                                 ʳ⟨≡⟩ fmap-comp f head (uniform 1)) ⟩
    sample (fmap-F f (fmap-F head (uniform 1))) a
    ∎

  coin-is-fair : ∀ b → negpow2 1 ≡ sample coin b
  coin-is-fair b =
    negpow2 1
      ≡⟨ uniform-is-uniform 1 (b ∷ []) ⟩
    sample (uniform 1) (b ∷ [])
      ≡⟨ injection-invariant head head1-Inj (uniform 1) ((b ∷ [])) ⟩
    sample (fmap head (uniform 1)) b
      ≡⟨ refl ⟩
    sample coin b
    ∎

-- The FPF paper/thesis suggests the following laws as well:
-- Commutativity:
-- a >>= λ x → b >>= λ y → f a b ≡D b >>= λ y → a >>= λ x → f a b
--
-- Distribution Irrelevance:
-- Given c : D A, f : A → D B, y : A, if for any x in the support of c,
-- sample (f x) y ≡ v for a fixed v, then sample (c >>= f) y ≡ v.
--
-- Distribution Isomorphism:
-- For any bijection f and any distributions c₁ and c₂, if f is the
-- relation between c₁ and c₂ then sampling x from c₁ is the same as
-- sampling f x from c₂.
--
-- Repeat Equivalence (irrelevant, we have no repeat)
--
-- Identical Until Bad
-- If c₁ and c₂ have the same chance of going bad and the distributions are
-- identical provided they do not go bad, then their difference is upper
-- bounded by their chance to go bad.
--
-- These laws are formulated with sequencing in mind, so rather than just
-- speaking of distributions, they speak of distributions and steps.  Maybe
-- that can be taken out to be a separate law?
