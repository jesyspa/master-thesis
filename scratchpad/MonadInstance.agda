module MonadInstance where

open import Category.Monad using (RawMonad)

data Unit (a : Set) : Set where
  unit : Unit a

instance
  UnitMonad : RawMonad Unit
  RawMonad.return UnitMonad _ = unit
  RawMonad._>>=_ UnitMonad _ _ = unit

