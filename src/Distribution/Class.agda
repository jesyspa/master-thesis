module Distribution.Class where

open import ThesisPrelude
open import Carrier.Class
open import Utility.BitVec
open import Algebra.Monad

record DistMonad (D : Set → Set) : Set₁ where
  infix 4 _≡D_
  field
    carrier : Set
    uniform : ∀ n → D (BitVec n)
    sample : ∀{A} → {{_ : Eq A}} → D A → A → carrier
    _≡D_ : ∀{A} → {{_ : Eq A}} → D A → D A → Set
    overlap {{super-monad}} : Carrier carrier
    overlap {{super-carrier}} : Monad D

open DistMonad {{...}} public

record DistMonadProp (D : Set → Set) {{DM : DistMonad D}} : Set₂ where
  field
    is-monad : MonadProps D
    uniform-is-uniform : ∀{n} (xs : BitVec n) → negpow2 n ≡ DistMonad.sample DM (DistMonad.uniform DM n) xs

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

open DistMonadProp {{...}} public
