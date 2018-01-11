open import Distribution.Class using (DistMonad)
module Distribution.PropsClass (F : Set → Set) {{DF : DistMonad F}} where

open DistMonad {{...}}

open import ThesisPrelude
open import Carrier.Class
open import Algebra.MonadProps F
open import Algebra.FunctorProps F
open import Utility.Vector.BitVec
open import Algebra.Function

record DistMonadProps : Set₂ where
  field
    is-monad : MonadProps
    sample-invariant : ∀ {A} {{_ : Eq A}} {D₁ D₂ : F A} → D₁ ≡D D₂ → (a : A) → sample D₁ a ≡ sample D₂ a
    uniform-is-uniform : ∀ n (xs : BitVec n) → negpow2 n ≡ sample (uniform {{DF}} n) xs
    uniform-bijection-invariant : ∀ n (f : BitVec n → BitVec n)
                                → Bijective f
                                → fmap-F f (uniform n) ≡D uniform n

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
