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

open DistMonadProp {{...}} public
