module Monoid where

open import MyPrelude

record Monoid (A : Set) : Set where
  infixr 6 _<>_
  field
    mempty : A
    _<>_ : A → A → A
    assoc : (a b c : A) → a <> (b <> c) ≡ (a <> b) <> c
    left-identity : (a : A) → a ≡ mempty <> a
    right-identity : (a : A) → a ≡ a <> mempty

open Monoid {{...}} public

{-# DISPLAY Monoid.mempty _ = mempty #-}
{-# DISPLAY Monoid._<>_ _ a b = a <> b #-}

mconcat : ∀{A : Set} {{MonA : Monoid A}} → List A → A
mconcat = foldr _<>_ mempty 

